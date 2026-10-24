import SmallRowPrefixBoolean
import SmallDegreeProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
5 vertices with seven arrows and total degree at least two at each vertex. -/
namespace Delivery.SmallBudgetSevenOrder5
open FiniteGame Extremal RowPrefix SmallDegreeProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e : Nat) : Rows 5 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | _ => e

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16]
  | 2 => [3,5,9,17,6,10,18,12,20,24]
  | 3 => [7,11,19,13,21,25,14,22,26,28]
  | 4 => [15,23,27,29,30]
  | 5 => [31]
  | _ => []

theorem cover (d : Fin 6) : RowCover 5 d.val (choices d.val) := by
  revert d
  decide +kernel

def profile0_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node3 : Upper (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [0,0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [0,0,0] 2 (by decide) (choices 3) [] profile0_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [0,0,0] (choices 3) [] profile0_node3_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile0_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node2 : Upper (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [0,0] 2 (by decide) (choices 0) [0] profile0_node2_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [0,0] (choices 0) [0] profile0_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node3

def profile0_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node1 : Upper (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [0] 2 (by decide) (choices 0) [0] profile0_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [0] (choices 0) [0] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node2

def profile0_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node0 : Upper (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [] 2 (by decide) (choices 0) [0] profile0_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [] (choices 0) [0] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=5) [2,2,2,24,33]) (R (n:=5) [2,2,2,24,33]) [] 2 := profile0_node0

def profile1_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 0), upper := (rows 1 2 4 15 31), lower := (rows 1 2 4 15 31), losses := [] }

theorem profile1_node5 : Upper (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0,0,7,15] 2 :=
  bound_sound (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0,0,7,15] 2 profile1_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0,0,7,15] 2 profile1_node5_cert).mp (by decide +kernel))

def profile1_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node4 : Upper (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0,0,7] 2 := by
  apply routed_branch (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0,0,7] 2 (by decide) (choices 4) [15] profile1_node4_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0,0,7] (choices 4) [15] profile1_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node5

def profile1_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node3 : Upper (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0,0] 2 (by decide) (choices 3) [7] profile1_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0,0] (choices 3) [7] profile1_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node4

def profile1_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node2 : Upper (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0] 2 (by decide) (choices 0) [0] profile1_node2_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0,0] (choices 0) [0] profile1_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node3

def profile1_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node1 : Upper (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0] 2 (by decide) (choices 0) [0] profile1_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [0] (choices 0) [0] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node2

def profile1_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node0 : Upper (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [] 2 (by decide) (choices 0) [0] profile1_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [] (choices 0) [0] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node1

theorem profile1 : Upper (D (n:=5) [2,2,2,25,32]) (R (n:=5) [2,2,2,25,32]) [] 2 := profile1_node0

def profile2_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node1 : Upper (D (n:=5) [2,2,3,24,32]) (R (n:=5) [2,2,3,24,32]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,3,24,32]) (R (n:=5) [2,2,3,24,32]) [0] 2 (by decide) (choices 0) [] profile2_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,3,24,32]) (R (n:=5) [2,2,3,24,32]) [0] (choices 0) [] profile2_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile2_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node0 : Upper (D (n:=5) [2,2,3,24,32]) (R (n:=5) [2,2,3,24,32]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,3,24,32]) (R (n:=5) [2,2,3,24,32]) [] 2 (by decide) (choices 0) [0] profile2_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,3,24,32]) (R (n:=5) [2,2,3,24,32]) [] (choices 0) [0] profile2_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node1

theorem profile2 : Upper (D (n:=5) [2,2,3,24,32]) (R (n:=5) [2,2,3,24,32]) [] 2 := profile2_node0

def profile3_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node3 : Upper (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [0,0,16] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [0,0,16] 2 (by decide) (choices 2) [] profile3_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [0,0,16] (choices 2) [] profile3_node3_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile3_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node2 : Upper (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [0,0] 2 (by decide) (choices 1) [16] profile3_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [0,0] (choices 1) [16] profile3_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node3

def profile3_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node1 : Upper (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [0] 2 (by decide) (choices 0) [0] profile3_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [0] (choices 0) [0] profile3_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node2

def profile3_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node0 : Upper (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [] 2 (by decide) (choices 0) [0] profile3_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [] (choices 0) [0] profile3_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node1

theorem profile3 : Upper (D (n:=5) [2,2,9,16,34]) (R (n:=5) [2,2,9,16,34]) [] 2 := profile3_node0

def profile4_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 5 26 31), lower := (rows 1 2 5 26 16), losses := [{ target := 0, region := (rows 0 31 4 24 16), good := (rows 2 2 6 26 26) }] }

theorem profile4_node4 : Upper (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,1,18] 2 :=
  bound_sound (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,1,18] 2 profile4_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,1,18] 2 profile4_node4_cert).mp (by decide +kernel))

def profile4_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node3 : Upper (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,1] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,1] 2 (by decide) (choices 2) [18] profile4_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,1] (choices 2) [18] profile4_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node4

def profile4_node6_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 6 25 31), lower := (rows 1 2 6 25 16), losses := [{ target := 1, region := (rows 31 0 4 24 16), good := (rows 1 1 5 25 25) }] }

theorem profile4_node6 : Upper (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,2,17] 2 :=
  bound_sound (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,2,17] 2 profile4_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,2,17] 2 profile4_node6_cert).mp (by decide +kernel))

def profile4_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node5 : Upper (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,2] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,2] 2 (by decide) (choices 2) [17] profile4_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,2] (choices 2) [17] profile4_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node6

def profile4_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node7 : Upper (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,8] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,8] 2 (by decide) (choices 2) [] profile4_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,8] (choices 2) [] profile4_node7_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile4_node9_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 20 11 31), lower := (rows 1 2 20 11 16), losses := [] }

theorem profile4_node9 : Upper (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,16,3] 2 :=
  bound_sound (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,16,3] 2 profile4_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,16,3] 2 profile4_node9_cert).mp (by decide +kernel))

def profile4_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node8 : Upper (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,16] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,16] 2 (by decide) (choices 2) [3] profile4_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0,16] (choices 2) [3] profile4_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node9

def profile4_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node2 : Upper (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0] 2 (by decide) (choices 1) [1,2,8,16] profile4_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0,0] (choices 1) [1,2,8,16] profile4_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node3
  · exact profile4_node5
  · exact profile4_node7
  · exact profile4_node8

def profile4_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node1 : Upper (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0] 2 (by decide) (choices 0) [0] profile4_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [0] (choices 0) [0] profile4_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node2

def profile4_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node0 : Upper (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [] 2 (by decide) (choices 0) [0] profile4_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [] (choices 0) [0] profile4_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node1

theorem profile4 : Upper (D (n:=5) [2,2,9,17,33]) (R (n:=5) [2,2,9,17,33]) [] 2 := profile4_node0

def profile5_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 0), upper := (rows 1 2 12 11 31), lower := (rows 1 2 12 11 31), losses := [] }

theorem profile5_node5 : Upper (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0,8,3,15] 2 :=
  bound_sound (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0,8,3,15] 2 profile5_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0,8,3,15] 2 profile5_node5_cert).mp (by decide +kernel))

def profile5_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node4 : Upper (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0,8,3] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0,8,3] 2 (by decide) (choices 4) [15] profile5_node4_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0,8,3] (choices 4) [15] profile5_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile5_node5

def profile5_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node3 : Upper (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0,8] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0,8] 2 (by decide) (choices 2) [3] profile5_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0,8] (choices 2) [3] profile5_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile5_node4

def profile5_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node2 : Upper (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0] 2 (by decide) (choices 1) [8] profile5_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0,0] (choices 1) [8] profile5_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile5_node3

def profile5_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node1 : Upper (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0] 2 (by decide) (choices 0) [0] profile5_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [0] (choices 0) [0] profile5_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile5_node2

def profile5_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node0 : Upper (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [] 2 (by decide) (choices 0) [0] profile5_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [] (choices 0) [0] profile5_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile5_node1

theorem profile5 : Upper (D (n:=5) [2,2,9,18,32]) (R (n:=5) [2,2,9,18,32]) [] 2 := profile5_node0

def profile6_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 20 27 23), lower := (rows 1 2 20 27 16), losses := [] }

theorem profile6_node4 : Upper (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0,0,16,19] 2 :=
  bound_sound (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0,0,16,19] 2 profile6_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0,0,16,19] 2 profile6_node4_cert).mp (by decide +kernel))

def profile6_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node3 : Upper (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0,0,16] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0,0,16] 2 (by decide) (choices 3) [19] profile6_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0,0,16] (choices 3) [19] profile6_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node4

def profile6_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node2 : Upper (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0,0] 2 (by decide) (choices 1) [16] profile6_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0,0] (choices 1) [16] profile6_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node3

def profile6_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node1 : Upper (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0] 2 (by decide) (choices 0) [0] profile6_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [0] (choices 0) [0] profile6_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node2

def profile6_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node0 : Upper (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [] 2 (by decide) (choices 0) [0] profile6_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [] (choices 0) [0] profile6_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node1

theorem profile6 : Upper (D (n:=5) [2,2,9,24,26]) (R (n:=5) [2,2,9,24,26]) [] 2 := profile6_node0

def profile7_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 5 27 30), lower := (rows 1 2 5 27 16), losses := [] }

theorem profile7_node4 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1,19] 2 :=
  bound_sound (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1,19] 2 profile7_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1,19] 2 profile7_node4_cert).mp (by decide +kernel))

def profile7_node6_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 2 5 30 27), lower := (rows 1 2 5 30 27), losses := [] }

theorem profile7_node6 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1,22,11] 2 :=
  bound_sound (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1,22,11] 2 profile7_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1,22,11] 2 profile7_node6_cert).mp (by decide +kernel))

def profile7_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node5 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1,22] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1,22] 2 (by decide) (choices 3) [11] profile7_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1,22] (choices 3) [11] profile7_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node6

def profile7_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node3 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1] 2 (by decide) (choices 3) [19,22] profile7_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,1] (choices 3) [19,22] profile7_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile7_node4
  · exact profile7_node5

def profile7_node8_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 6 27 29), lower := (rows 1 2 6 27 16), losses := [] }

theorem profile7_node8 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2,19] 2 :=
  bound_sound (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2,19] 2 profile7_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2,19] 2 profile7_node8_cert).mp (by decide +kernel))

def profile7_node10_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 1 2 6 29 27), lower := (rows 1 2 6 29 27), losses := [] }

theorem profile7_node10 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2,21,11] 2 :=
  bound_sound (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2,21,11] 2 profile7_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2,21,11] 2 profile7_node10_cert).mp (by decide +kernel))

def profile7_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node9 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2,21] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2,21] 2 (by decide) (choices 3) [11] profile7_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2,21] (choices 3) [11] profile7_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node10

def profile7_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node7 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2] 2 (by decide) (choices 3) [19,21] profile7_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,2] (choices 3) [19,21] profile7_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile7_node8
  · exact profile7_node9

def profile7_node12_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 12 27 23), lower := (rows 1 2 12 27 16), losses := [] }

theorem profile7_node12 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,8,19] 2 :=
  bound_sound (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,8,19] 2 profile7_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,8,19] 2 profile7_node12_cert).mp (by decide +kernel))

def profile7_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node11 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,8] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,8] 2 (by decide) (choices 3) [19] profile7_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0,8] (choices 3) [19] profile7_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node12

def profile7_node2_route : Route 5 := (fun mask => match mask with | 16 => (8,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile7_node2 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0] 2 (by decide) (choices 1) [1,2,8] profile7_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0,0] (choices 1) [1,2,8] profile7_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node3
  · exact profile7_node7
  · exact profile7_node11

def profile7_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node1 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0] 2 (by decide) (choices 0) [0] profile7_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [0] (choices 0) [0] profile7_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node2

def profile7_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node0 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [] 2 (by decide) (choices 0) [0] profile7_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [] (choices 0) [0] profile7_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node1

theorem profile7 : Upper (D (n:=5) [2,2,9,25,25]) (R (n:=5) [2,2,9,25,25]) [] 2 := profile7_node0

def profile8_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node3 : Upper (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0,1] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0,1] 2 (by decide) (choices 2) [] profile8_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0,1] (choices 2) [] profile8_node3_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile8_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node4 : Upper (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0,2] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0,2] 2 (by decide) (choices 2) [] profile8_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0,2] (choices 2) [] profile8_node4_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile8_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node5 : Upper (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0,16] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0,16] 2 (by decide) (choices 2) [] profile8_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0,16] (choices 2) [] profile8_node5_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile8_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node2 : Upper (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0] 2 (by decide) (choices 1) [1,2,16] profile8_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0,0] (choices 1) [1,2,16] profile8_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node3
  · exact profile8_node4
  · exact profile8_node5

def profile8_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node1 : Upper (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0] 2 (by decide) (choices 0) [0] profile8_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [0] (choices 0) [0] profile8_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node2

def profile8_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node0 : Upper (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [] 2 (by decide) (choices 0) [0] profile8_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [] (choices 0) [0] profile8_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node1

theorem profile8 : Upper (D (n:=5) [2,2,10,16,33]) (R (n:=5) [2,2,10,16,33]) [] 2 := profile8_node0

def profile9_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 2 5 14 31), lower := (rows 1 2 5 14 31), losses := [] }

theorem profile9_node5 : Upper (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,1,6,15] 2 :=
  bound_sound (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,1,6,15] 2 profile9_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,1,6,15] 2 profile9_node5_cert).mp (by decide +kernel))

def profile9_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node4 : Upper (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,1,6] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,1,6] 2 (by decide) (choices 4) [15] profile9_node4_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,1,6] (choices 4) [15] profile9_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node5

def profile9_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node3 : Upper (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,1] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,1] 2 (by decide) (choices 2) [6] profile9_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,1] (choices 2) [6] profile9_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node4

def profile9_node8_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 1 2 6 13 31), lower := (rows 1 2 6 13 31), losses := [] }

theorem profile9_node8 : Upper (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,2,5,15] 2 :=
  bound_sound (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,2,5,15] 2 profile9_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,2,5,15] 2 profile9_node8_cert).mp (by decide +kernel))

def profile9_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node7 : Upper (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,2,5] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,2,5] 2 (by decide) (choices 4) [15] profile9_node7_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,2,5] (choices 4) [15] profile9_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node8

def profile9_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node6 : Upper (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,2] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,2] 2 (by decide) (choices 2) [5] profile9_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,2] (choices 2) [5] profile9_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node7

def profile9_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node9 : Upper (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,8] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,8] 2 (by decide) (choices 2) [] profile9_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0,8] (choices 2) [] profile9_node9_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile9_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node2 : Upper (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0] 2 (by decide) (choices 1) [1,2,8] profile9_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0,0] (choices 1) [1,2,8] profile9_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node3
  · exact profile9_node6
  · exact profile9_node9

def profile9_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node1 : Upper (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0] 2 (by decide) (choices 0) [0] profile9_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [0] (choices 0) [0] profile9_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node2

def profile9_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node0 : Upper (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [] 2 (by decide) (choices 0) [0] profile9_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [] (choices 0) [0] profile9_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node1

theorem profile9 : Upper (D (n:=5) [2,2,10,17,32]) (R (n:=5) [2,2,10,17,32]) [] 2 := profile9_node0

def profile10_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 2 5 30 23), lower := (rows 1 2 5 30 23), losses := [] }

theorem profile10_node5 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,1,22,7] 2 :=
  bound_sound (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,1,22,7] 2 profile10_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,1,22,7] 2 profile10_node5_cert).mp (by decide +kernel))

def profile10_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node4 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,1,22] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,1,22] 2 (by decide) (choices 3) [7] profile10_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,1,22] (choices 3) [7] profile10_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node5

def profile10_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node3 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,1] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,1] 2 (by decide) (choices 3) [22] profile10_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,1] (choices 3) [22] profile10_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node4

def profile10_node8_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 1 2 6 29 23), lower := (rows 1 2 6 29 23), losses := [] }

theorem profile10_node8 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,2,21,7] 2 :=
  bound_sound (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,2,21,7] 2 profile10_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,2,21,7] 2 profile10_node8_cert).mp (by decide +kernel))

def profile10_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node7 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,2,21] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,2,21] 2 (by decide) (choices 3) [7] profile10_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,2,21] (choices 3) [7] profile10_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node8

def profile10_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node6 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,2] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,2] 2 (by decide) (choices 3) [21] profile10_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,2] (choices 3) [21] profile10_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node7

def profile10_node11_cert : Bound 5 := { allowed := (rows 0 0 0 0 0), upper := (rows 1 2 20 15 23), lower := (rows 1 2 20 15 23), losses := [] }

theorem profile10_node11 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,16,7,7] 2 :=
  bound_sound (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,16,7,7] 2 profile10_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,16,7,7] 2 profile10_node11_cert).mp (by decide +kernel))

def profile10_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node10 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,16,7] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,16,7] 2 (by decide) (choices 3) [7] profile10_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,16,7] (choices 3) [7] profile10_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node11

def profile10_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node9 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,16] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,16] 2 (by decide) (choices 3) [7] profile10_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0,16] (choices 3) [7] profile10_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node10

def profile10_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node2 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0] 2 (by decide) (choices 1) [1,2,16] profile10_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0,0] (choices 1) [1,2,16] profile10_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node3
  · exact profile10_node6
  · exact profile10_node9

def profile10_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node1 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0] 2 (by decide) (choices 0) [0] profile10_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [0] (choices 0) [0] profile10_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node2

def profile10_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node0 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [] 2 (by decide) (choices 0) [0] profile10_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [] (choices 0) [0] profile10_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node1

theorem profile10 : Upper (D (n:=5) [2,2,10,24,25]) (R (n:=5) [2,2,10,24,25]) [] 2 := profile10_node0

def profile11_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node1 : Upper (D (n:=5) [2,2,11,16,32]) (R (n:=5) [2,2,11,16,32]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,11,16,32]) (R (n:=5) [2,2,11,16,32]) [0] 2 (by decide) (choices 0) [] profile11_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,11,16,32]) (R (n:=5) [2,2,11,16,32]) [0] (choices 0) [] profile11_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile11_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node0 : Upper (D (n:=5) [2,2,11,16,32]) (R (n:=5) [2,2,11,16,32]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,11,16,32]) (R (n:=5) [2,2,11,16,32]) [] 2 (by decide) (choices 0) [0] profile11_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,11,16,32]) (R (n:=5) [2,2,11,16,32]) [] (choices 0) [0] profile11_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node1

theorem profile11 : Upper (D (n:=5) [2,2,11,16,32]) (R (n:=5) [2,2,11,16,32]) [] 2 := profile11_node0

def profile12_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node1 : Upper (D (n:=5) [2,2,11,24,24]) (R (n:=5) [2,2,11,24,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,11,24,24]) (R (n:=5) [2,2,11,24,24]) [0] 2 (by decide) (choices 0) [] profile12_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,11,24,24]) (R (n:=5) [2,2,11,24,24]) [0] (choices 0) [] profile12_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile12_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node0 : Upper (D (n:=5) [2,2,11,24,24]) (R (n:=5) [2,2,11,24,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,11,24,24]) (R (n:=5) [2,2,11,24,24]) [] 2 (by decide) (choices 0) [0] profile12_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,11,24,24]) (R (n:=5) [2,2,11,24,24]) [] (choices 0) [0] profile12_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node1

theorem profile12 : Upper (D (n:=5) [2,2,11,24,24]) (R (n:=5) [2,2,11,24,24]) [] 2 := profile12_node0

def profile13_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node1 : Upper (D (n:=5) [2,2,16,16,27]) (R (n:=5) [2,2,16,16,27]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,16,27]) (R (n:=5) [2,2,16,16,27]) [0] 2 (by decide) (choices 0) [] profile13_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,16,27]) (R (n:=5) [2,2,16,16,27]) [0] (choices 0) [] profile13_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile13_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node0 : Upper (D (n:=5) [2,2,16,16,27]) (R (n:=5) [2,2,16,16,27]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,16,27]) (R (n:=5) [2,2,16,16,27]) [] 2 (by decide) (choices 0) [0] profile13_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,16,27]) (R (n:=5) [2,2,16,16,27]) [] (choices 0) [0] profile13_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node1

theorem profile13 : Upper (D (n:=5) [2,2,16,16,27]) (R (n:=5) [2,2,16,16,27]) [] 2 := profile13_node0

def profile14_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 21 26 27), lower := (rows 1 2 21 26 16), losses := [{ target := 0, region := (rows 0 31 4 28 16), good := (rows 2 2 30 26 26) },{ target := 1, region := (rows 31 0 28 8 16), good := (rows 1 1 21 29 21) }] }

theorem profile14_node4 : Upper (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,17,18] 2 :=
  bound_sound (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,17,18] 2 profile14_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,17,18] 2 profile14_node4_cert).mp (by decide +kernel))

def profile14_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node3 : Upper (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,17] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,17] 2 (by decide) (choices 2) [18] profile14_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,17] (choices 2) [18] profile14_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node4

def profile14_node6_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 22 25 27), lower := (rows 1 2 22 25 16), losses := [{ target := 0, region := (rows 0 31 28 8 16), good := (rows 2 2 22 30 22) },{ target := 1, region := (rows 31 0 4 28 16), good := (rows 1 1 29 25 25) }] }

theorem profile14_node6 : Upper (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,18,17] 2 :=
  bound_sound (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,18,17] 2 profile14_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,18,17] 2 profile14_node6_cert).mp (by decide +kernel))

def profile14_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node5 : Upper (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,18] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,18] 2 (by decide) (choices 2) [17] profile14_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,18] (choices 2) [17] profile14_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node6

def profile14_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node7 : Upper (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,24] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,24] 2 (by decide) (choices 2) [] profile14_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0,24] (choices 2) [] profile14_node7_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile14_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node2 : Upper (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0] 2 (by decide) (choices 2) [17,18,24] profile14_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0,0] (choices 2) [17,18,24] profile14_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node3
  · exact profile14_node5
  · exact profile14_node7

def profile14_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node1 : Upper (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0] 2 (by decide) (choices 0) [0] profile14_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [0] (choices 0) [0] profile14_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node2

def profile14_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node0 : Upper (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [] 2 (by decide) (choices 0) [0] profile14_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [] (choices 0) [0] profile14_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node1

theorem profile14 : Upper (D (n:=5) [2,2,16,17,26]) (R (n:=5) [2,2,16,17,26]) [] 2 := profile14_node0

def profile15_node5_cert : Bound 5 := { allowed := (rows 0 0 2 1 0), upper := (rows 1 2 13 26 27), lower := (rows 1 2 13 26 27), losses := [] }

theorem profile15_node5 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,9,18,11] 2 :=
  bound_sound (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,9,18,11] 2 profile15_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,9,18,11] 2 profile15_node5_cert).mp (by decide +kernel))

def profile15_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node4 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,9,18] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,9,18] 2 (by decide) (choices 3) [11] profile15_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,9,18] (choices 3) [11] profile15_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node5

def profile15_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node3 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,9] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,9] 2 (by decide) (choices 2) [18] profile15_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,9] (choices 2) [18] profile15_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node4

def profile15_node8_cert : Bound 5 := { allowed := (rows 0 0 1 2 0), upper := (rows 1 2 14 25 27), lower := (rows 1 2 14 25 27), losses := [] }

theorem profile15_node8 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,10,17,11] 2 :=
  bound_sound (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,10,17,11] 2 profile15_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,10,17,11] 2 profile15_node8_cert).mp (by decide +kernel))

def profile15_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node7 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,10,17] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,10,17] 2 (by decide) (choices 3) [11] profile15_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,10,17] (choices 3) [11] profile15_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node8

def profile15_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node6 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,10] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,10] 2 (by decide) (choices 2) [17] profile15_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,10] (choices 2) [17] profile15_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node7

def profile15_node11_cert : Bound 5 := { allowed := (rows 0 0 3 0 0), upper := (rows 1 2 28 11 27), lower := (rows 1 2 28 11 27), losses := [] }

theorem profile15_node11 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,24,3,11] 2 :=
  bound_sound (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,24,3,11] 2 profile15_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,24,3,11] 2 profile15_node11_cert).mp (by decide +kernel))

def profile15_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node10 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,24,3] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,24,3] 2 (by decide) (choices 3) [11] profile15_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,24,3] (choices 3) [11] profile15_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node11

def profile15_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node9 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,24] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,24] 2 (by decide) (choices 2) [3] profile15_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0,24] (choices 2) [3] profile15_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node10

def profile15_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node2 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0] 2 (by decide) (choices 2) [9,10,24] profile15_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0,0] (choices 2) [9,10,24] profile15_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node3
  · exact profile15_node6
  · exact profile15_node9

def profile15_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node1 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0] 2 (by decide) (choices 0) [0] profile15_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [0] (choices 0) [0] profile15_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node2

def profile15_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node0 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [] 2 (by decide) (choices 0) [0] profile15_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [] (choices 0) [0] profile15_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node1

theorem profile15 : Upper (D (n:=5) [2,2,16,18,25]) (R (n:=5) [2,2,16,18,25]) [] 2 := profile15_node0

def profile16_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node1 : Upper (D (n:=5) [2,2,16,19,24]) (R (n:=5) [2,2,16,19,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,19,24]) (R (n:=5) [2,2,16,19,24]) [0] 2 (by decide) (choices 0) [] profile16_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,19,24]) (R (n:=5) [2,2,16,19,24]) [0] (choices 0) [] profile16_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile16_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node0 : Upper (D (n:=5) [2,2,16,19,24]) (R (n:=5) [2,2,16,19,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,16,19,24]) (R (n:=5) [2,2,16,19,24]) [] 2 (by decide) (choices 0) [0] profile16_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,16,19,24]) (R (n:=5) [2,2,16,19,24]) [] (choices 0) [0] profile16_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile16_node1

theorem profile16 : Upper (D (n:=5) [2,2,16,19,24]) (R (n:=5) [2,2,16,19,24]) [] 2 := profile16_node0

def profile17_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 7 25 30), lower := (rows 1 2 7 25 16), losses := [{ target := 1, region := (rows 31 0 4 24 16), good := (rows 1 1 5 25 25) }] }

theorem profile17_node4 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,17] 2 :=
  bound_sound (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,17] 2 profile17_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,17] 2 profile17_node4_cert).mp (by decide +kernel))

def profile17_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 7 26 29), lower := (rows 1 2 7 26 16), losses := [{ target := 0, region := (rows 0 31 4 24 16), good := (rows 2 2 6 26 26) }] }

theorem profile17_node5 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,18] 2 :=
  bound_sound (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,18] 2 profile17_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,18] 2 profile17_node5_cert).mp (by decide +kernel))

def profile17_node7_cert : Bound 5 := { allowed := (rows 0 0 0 3 0), upper := (rows 1 2 7 28 27), lower := (rows 1 2 7 28 27), losses := [] }

theorem profile17_node7 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,20,11] 2 :=
  bound_sound (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,20,11] 2 profile17_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,20,11] 2 profile17_node7_cert).mp (by decide +kernel))

def profile17_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node6 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,20] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,20] 2 (by decide) (choices 3) [11] profile17_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3,20] (choices 3) [11] profile17_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile17_node7

def profile17_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node3 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3] 2 (by decide) (choices 2) [17,18,20] profile17_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,3] (choices 2) [17,18,20] profile17_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile17_node4
  · exact profile17_node5
  · exact profile17_node6

def profile17_node9_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 13 26 23), lower := (rows 1 2 13 26 16), losses := [{ target := 0, region := (rows 0 31 4 24 16), good := (rows 2 2 14 26 26) },{ target := 1, region := (rows 31 0 12 8 16), good := (rows 1 1 13 29 17) }] }

theorem profile17_node9 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,9,18] 2 :=
  bound_sound (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,9,18] 2 profile17_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,9,18] 2 profile17_node9_cert).mp (by decide +kernel))

def profile17_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node8 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,9] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,9] 2 (by decide) (choices 2) [18] profile17_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,9] (choices 2) [18] profile17_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile17_node9

def profile17_node11_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 14 25 23), lower := (rows 1 2 14 25 16), losses := [{ target := 0, region := (rows 0 31 12 8 16), good := (rows 2 2 14 30 18) },{ target := 1, region := (rows 31 0 4 24 16), good := (rows 1 1 13 25 25) }] }

theorem profile17_node11 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,10,17] 2 :=
  bound_sound (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,10,17] 2 profile17_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,10,17] 2 profile17_node11_cert).mp (by decide +kernel))

def profile17_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node10 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,10] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,10] 2 (by decide) (choices 2) [17] profile17_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,10] (choices 2) [17] profile17_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile17_node11

def profile17_node13_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 21 11 30), lower := (rows 1 2 21 11 16), losses := [{ target := 1, region := (rows 31 0 20 8 16), good := (rows 1 1 21 9 21) }] }

theorem profile17_node13 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,17,3] 2 :=
  bound_sound (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,17,3] 2 profile17_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,17,3] 2 profile17_node13_cert).mp (by decide +kernel))

def profile17_node14_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 21 14 27), lower := (rows 1 2 21 14 16), losses := [{ target := 0, region := (rows 0 31 4 12 16), good := (rows 2 2 30 14 18) },{ target := 1, region := (rows 31 0 20 8 16), good := (rows 1 1 21 13 21) }] }

theorem profile17_node14 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,17,6] 2 :=
  bound_sound (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,17,6] 2 profile17_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,17,6] 2 profile17_node14_cert).mp (by decide +kernel))

def profile17_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node12 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,17] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,17] 2 (by decide) (choices 2) [3,6] profile17_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,17] (choices 2) [3,6] profile17_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile17_node13
  · exact profile17_node14

def profile17_node16_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 22 11 29), lower := (rows 1 2 22 11 16), losses := [{ target := 0, region := (rows 0 31 20 8 16), good := (rows 2 2 22 10 22) }] }

theorem profile17_node16 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,18,3] 2 :=
  bound_sound (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,18,3] 2 profile17_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,18,3] 2 profile17_node16_cert).mp (by decide +kernel))

def profile17_node17_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 22 13 27), lower := (rows 1 2 22 13 16), losses := [{ target := 0, region := (rows 0 31 20 8 16), good := (rows 2 2 22 14 22) },{ target := 1, region := (rows 31 0 4 12 16), good := (rows 1 1 29 13 17) }] }

theorem profile17_node17 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,18,5] 2 :=
  bound_sound (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,18,5] 2 profile17_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,18,5] 2 profile17_node17_cert).mp (by decide +kernel))

def profile17_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node15 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,18] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,18] 2 (by decide) (choices 2) [3,5] profile17_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,18] (choices 2) [3,5] profile17_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile17_node16
  · exact profile17_node17

def profile17_node20_cert : Bound 5 := { allowed := (rows 0 0 3 0 0), upper := (rows 1 2 28 11 23), lower := (rows 1 2 28 11 23), losses := [] }

theorem profile17_node20 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,24,3,7] 2 :=
  bound_sound (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,24,3,7] 2 profile17_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,24,3,7] 2 profile17_node20_cert).mp (by decide +kernel))

def profile17_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node19 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,24,3] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,24,3] 2 (by decide) (choices 3) [7] profile17_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,24,3] (choices 3) [7] profile17_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile17_node20

def profile17_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node18 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,24] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,24] 2 (by decide) (choices 2) [3] profile17_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0,24] (choices 2) [3] profile17_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile17_node19

def profile17_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node2 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile17_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0,0] (choices 2) [3,9,10,17,18,24] profile17_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile17_node3
  · exact profile17_node8
  · exact profile17_node10
  · exact profile17_node12
  · exact profile17_node15
  · exact profile17_node18

def profile17_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node1 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0] 2 (by decide) (choices 0) [0] profile17_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [0] (choices 0) [0] profile17_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile17_node2

def profile17_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node0 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [] 2 (by decide) (choices 0) [0] profile17_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [] (choices 0) [0] profile17_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile17_node1

theorem profile17 : Upper (D (n:=5) [2,2,17,17,25]) (R (n:=5) [2,2,17,17,25]) [] 2 := profile17_node0

def profile18_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 10), upper := (rows 1 2 13 11 30), lower := (rows 1 2 13 11 16), losses := [{ target := 0, region := (rows 0 31 4 8 20), good := (rows 2 2 30 10 18) },{ target := 1, region := (rows 31 0 12 8 16), good := (rows 1 1 13 13 17) }] }

theorem profile18_node4 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9,3] 2 :=
  bound_sound (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9,3] 2 profile18_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9,3] 2 profile18_node4_cert).mp (by decide +kernel))

def profile18_node6_cert : Bound 5 := { allowed := (rows 0 0 2 1 0), upper := (rows 1 2 13 14 27), lower := (rows 1 2 13 14 27), losses := [] }

theorem profile18_node6 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9,6,11] 2 :=
  bound_sound (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9,6,11] 2 profile18_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9,6,11] 2 profile18_node6_cert).mp (by decide +kernel))

def profile18_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node5 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9,6] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9,6] 2 (by decide) (choices 3) [11] profile18_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9,6] (choices 3) [11] profile18_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile18_node6

def profile18_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node3 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9] 2 (by decide) (choices 2) [3,6] profile18_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,9] (choices 2) [3,6] profile18_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile18_node4
  · exact profile18_node5

def profile18_node8_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 2 14 11 29), lower := (rows 1 2 14 11 16), losses := [{ target := 0, region := (rows 0 31 12 8 16), good := (rows 2 2 14 14 18) },{ target := 1, region := (rows 31 0 4 8 20), good := (rows 1 1 29 9 17) }] }

theorem profile18_node8 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10,3] 2 :=
  bound_sound (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10,3] 2 profile18_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10,3] 2 profile18_node8_cert).mp (by decide +kernel))

def profile18_node10_cert : Bound 5 := { allowed := (rows 0 0 1 2 0), upper := (rows 1 2 14 13 27), lower := (rows 1 2 14 13 27), losses := [] }

theorem profile18_node10 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10,5,11] 2 :=
  bound_sound (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10,5,11] 2 profile18_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10,5,11] 2 profile18_node10_cert).mp (by decide +kernel))

def profile18_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node9 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10,5] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10,5] 2 (by decide) (choices 3) [11] profile18_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10,5] (choices 3) [11] profile18_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile18_node10

def profile18_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node7 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10] 2 (by decide) (choices 2) [3,5] profile18_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0,10] (choices 2) [3,5] profile18_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile18_node8
  · exact profile18_node9

def profile18_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node2 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0] 2 (by decide) (choices 2) [9,10] profile18_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0,0] (choices 2) [9,10] profile18_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile18_node3
  · exact profile18_node7

def profile18_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node1 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0] 2 (by decide) (choices 0) [0] profile18_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [0] (choices 0) [0] profile18_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile18_node2

def profile18_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node0 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [] 2 (by decide) (choices 0) [0] profile18_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [] (choices 0) [0] profile18_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile18_node1

theorem profile18 : Upper (D (n:=5) [2,2,17,18,24]) (R (n:=5) [2,2,17,18,24]) [] 2 := profile18_node0

def profile19_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile19_node3 : Upper (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [0,0,2] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [0,0,2] 2 (by decide) (choices 2) [] profile19_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [0,0,2] (choices 2) [] profile19_node3_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile19_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile19_node2 : Upper (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [0,0] 2 (by decide) (choices 1) [2] profile19_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [0,0] (choices 1) [2] profile19_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node3

def profile19_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile19_node1 : Upper (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [0] 2 (by decide) (choices 0) [0] profile19_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [0] (choices 0) [0] profile19_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node2

def profile19_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile19_node0 : Upper (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [] 2 (by decide) (choices 0) [0] profile19_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [] (choices 0) [0] profile19_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node1

theorem profile19 : Upper (D (n:=5) [2,3,9,16,33]) (R (n:=5) [2,3,9,16,33]) [] 2 := profile19_node0

def profile20_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 6 11 31), lower := (rows 1 2 6 11 16), losses := [] }

theorem profile20_node4 : Upper (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0,0,2,3] 2 :=
  bound_sound (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0,0,2,3] 2 profile20_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0,0,2,3] 2 profile20_node4_cert).mp (by decide +kernel))

def profile20_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node3 : Upper (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0,0,2] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0,0,2] 2 (by decide) (choices 2) [3] profile20_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0,0,2] (choices 2) [3] profile20_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node4

def profile20_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node2 : Upper (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0,0] 2 (by decide) (choices 1) [2] profile20_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0,0] (choices 1) [2] profile20_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node3

def profile20_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node1 : Upper (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0] 2 (by decide) (choices 0) [0] profile20_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [0] (choices 0) [0] profile20_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node2

def profile20_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node0 : Upper (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [] 2 (by decide) (choices 0) [0] profile20_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [] (choices 0) [0] profile20_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node1

theorem profile20 : Upper (D (n:=5) [2,3,9,17,32]) (R (n:=5) [2,3,9,17,32]) [] 2 := profile20_node0

def profile21_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 6 27 23), lower := (rows 1 2 6 27 16), losses := [] }

theorem profile21_node4 : Upper (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0,0,2,19] 2 :=
  bound_sound (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0,0,2,19] 2 profile21_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0,0,2,19] 2 profile21_node4_cert).mp (by decide +kernel))

def profile21_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node3 : Upper (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0,0,2] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0,0,2] 2 (by decide) (choices 3) [19] profile21_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0,0,2] (choices 3) [19] profile21_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node4

def profile21_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node2 : Upper (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0,0] 2 (by decide) (choices 1) [2] profile21_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0,0] (choices 1) [2] profile21_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node3

def profile21_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node1 : Upper (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0] 2 (by decide) (choices 0) [0] profile21_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [0] (choices 0) [0] profile21_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node2

def profile21_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node0 : Upper (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [] 2 := by
  apply routed_branch (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [] 2 (by decide) (choices 0) [0] profile21_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [] (choices 0) [0] profile21_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node1

theorem profile21 : Upper (D (n:=5) [2,3,9,24,25]) (R (n:=5) [2,3,9,24,25]) [] 2 := profile21_node0

def profile22_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile22_node3 : Upper (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [0,0,2] 2 := by
  apply routed_branch (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [0,0,2] 2 (by decide) (choices 2) [] profile22_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [0,0,2] (choices 2) [] profile22_node3_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile22_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile22_node2 : Upper (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [0,0] 2 (by decide) (choices 1) [2] profile22_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [0,0] (choices 1) [2] profile22_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node3

def profile22_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile22_node1 : Upper (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [0] 2 (by decide) (choices 0) [0] profile22_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [0] (choices 0) [0] profile22_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node2

def profile22_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile22_node0 : Upper (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [] 2 := by
  apply routed_branch (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [] 2 (by decide) (choices 0) [0] profile22_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [] (choices 0) [0] profile22_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node1

theorem profile22 : Upper (D (n:=5) [2,3,10,16,32]) (R (n:=5) [2,3,10,16,32]) [] 2 := profile22_node0

def profile23_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 0), upper := (rows 1 2 6 15 23), lower := (rows 1 2 6 15 23), losses := [] }

theorem profile23_node5 : Upper (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0,2,7,7] 2 :=
  bound_sound (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0,2,7,7] 2 profile23_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0,2,7,7] 2 profile23_node5_cert).mp (by decide +kernel))

def profile23_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node4 : Upper (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0,2,7] 2 := by
  apply routed_branch (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0,2,7] 2 (by decide) (choices 3) [7] profile23_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0,2,7] (choices 3) [7] profile23_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node5

def profile23_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node3 : Upper (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0,2] 2 := by
  apply routed_branch (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0,2] 2 (by decide) (choices 3) [7] profile23_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0,2] (choices 3) [7] profile23_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node4

def profile23_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node2 : Upper (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0] 2 (by decide) (choices 1) [2] profile23_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0,0] (choices 1) [2] profile23_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node3

def profile23_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node1 : Upper (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0] 2 (by decide) (choices 0) [0] profile23_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [0] (choices 0) [0] profile23_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node2

def profile23_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node0 : Upper (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [] 2 (by decide) (choices 0) [0] profile23_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [] (choices 0) [0] profile23_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node1

theorem profile23 : Upper (D (n:=5) [2,3,10,24,24]) (R (n:=5) [2,3,10,24,24]) [] 2 := profile23_node0

def profile24_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node3 : Upper (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [0,0,18] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [0,0,18] 2 (by decide) (choices 2) [] profile24_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [0,0,18] (choices 2) [] profile24_node3_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile24_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node2 : Upper (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [0,0] 2 (by decide) (choices 2) [18] profile24_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [0,0] (choices 2) [18] profile24_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node3

def profile24_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node1 : Upper (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [0] 2 (by decide) (choices 0) [0] profile24_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [0] (choices 0) [0] profile24_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node2

def profile24_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node0 : Upper (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [] 2 (by decide) (choices 0) [0] profile24_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [] (choices 0) [0] profile24_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node1

theorem profile24 : Upper (D (n:=5) [2,3,16,16,26]) (R (n:=5) [2,3,16,16,26]) [] 2 := profile24_node0

def profile25_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 7 26 27), lower := (rows 1 2 7 26 16), losses := [{ target := 0, region := (rows 0 31 4 24 16), good := (rows 2 2 6 26 26) }] }

theorem profile25_node4 : Upper (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,3,18] 2 :=
  bound_sound (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,3,18] 2 profile25_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,3,18] 2 profile25_node4_cert).mp (by decide +kernel))

def profile25_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node3 : Upper (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,3] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,3] 2 (by decide) (choices 2) [18] profile25_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,3] (choices 2) [18] profile25_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile25_node4

def profile25_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node5 : Upper (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,10] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,10] 2 (by decide) (choices 2) [] profile25_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,10] (choices 2) [] profile25_node5_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile25_node7_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 22 11 27), lower := (rows 1 2 22 11 16), losses := [{ target := 0, region := (rows 0 31 20 8 16), good := (rows 2 2 22 10 22) }] }

theorem profile25_node7 : Upper (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,18,3] 2 :=
  bound_sound (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,18,3] 2 profile25_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,18,3] 2 profile25_node7_cert).mp (by decide +kernel))

def profile25_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node6 : Upper (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,18] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,18] 2 (by decide) (choices 2) [3] profile25_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0,18] (choices 2) [3] profile25_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile25_node7

def profile25_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node2 : Upper (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0] 2 (by decide) (choices 2) [3,10,18] profile25_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0,0] (choices 2) [3,10,18] profile25_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node3
  · exact profile25_node5
  · exact profile25_node6

def profile25_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node1 : Upper (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0] 2 (by decide) (choices 0) [0] profile25_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [0] (choices 0) [0] profile25_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile25_node2

def profile25_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node0 : Upper (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [] 2 (by decide) (choices 0) [0] profile25_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [] (choices 0) [0] profile25_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile25_node1

theorem profile25 : Upper (D (n:=5) [2,3,16,17,25]) (R (n:=5) [2,3,16,17,25]) [] 2 := profile25_node0

def profile26_node5_cert : Bound 5 := { allowed := (rows 0 0 1 0 0), upper := (rows 1 2 14 11 27), lower := (rows 1 2 14 11 27), losses := [] }

theorem profile26_node5 : Upper (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0,10,3,11] 2 :=
  bound_sound (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0,10,3,11] 2 profile26_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0,10,3,11] 2 profile26_node5_cert).mp (by decide +kernel))

def profile26_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node4 : Upper (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0,10,3] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0,10,3] 2 (by decide) (choices 3) [11] profile26_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0,10,3] (choices 3) [11] profile26_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile26_node5

def profile26_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node3 : Upper (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0,10] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0,10] 2 (by decide) (choices 2) [3] profile26_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0,10] (choices 2) [3] profile26_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile26_node4

def profile26_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node2 : Upper (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0] 2 (by decide) (choices 2) [10] profile26_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0,0] (choices 2) [10] profile26_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile26_node3

def profile26_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node1 : Upper (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0] 2 (by decide) (choices 0) [0] profile26_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [0] (choices 0) [0] profile26_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile26_node2

def profile26_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node0 : Upper (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [] 2 (by decide) (choices 0) [0] profile26_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [] (choices 0) [0] profile26_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile26_node1

theorem profile26 : Upper (D (n:=5) [2,3,16,18,24]) (R (n:=5) [2,3,16,18,24]) [] 2 := profile26_node0

def profile27_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 7 11 30), lower := (rows 1 2 7 11 16), losses := [] }

theorem profile27_node4 : Upper (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,3,3] 2 :=
  bound_sound (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,3,3] 2 profile27_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,3,3] 2 profile27_node4_cert).mp (by decide +kernel))

def profile27_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 7 14 27), lower := (rows 1 2 7 14 16), losses := [{ target := 0, region := (rows 0 31 4 12 16), good := (rows 2 2 14 14 18) }] }

theorem profile27_node5 : Upper (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,3,6] 2 :=
  bound_sound (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,3,6] 2 profile27_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,3,6] 2 profile27_node5_cert).mp (by decide +kernel))

def profile27_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node3 : Upper (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,3] 2 := by
  apply routed_branch (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,3] 2 (by decide) (choices 2) [3,6] profile27_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,3] (choices 2) [3,6] profile27_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node4
  · exact profile27_node5

def profile27_node7_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 14 11 23), lower := (rows 1 2 14 11 16), losses := [{ target := 0, region := (rows 0 31 12 8 16), good := (rows 2 2 14 14 18) }] }

theorem profile27_node7 : Upper (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,10,3] 2 :=
  bound_sound (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,10,3] 2 profile27_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,10,3] 2 profile27_node7_cert).mp (by decide +kernel))

def profile27_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node6 : Upper (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,10] 2 := by
  apply routed_branch (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,10] 2 (by decide) (choices 2) [3] profile27_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0,10] (choices 2) [3] profile27_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node7

def profile27_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node2 : Upper (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0] 2 (by decide) (choices 2) [3,10] profile27_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0,0] (choices 2) [3,10] profile27_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node3
  · exact profile27_node6

def profile27_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node1 : Upper (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0] 2 (by decide) (choices 0) [0] profile27_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [0] (choices 0) [0] profile27_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node2

def profile27_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node0 : Upper (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [] 2 (by decide) (choices 0) [0] profile27_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [] (choices 0) [0] profile27_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node1

theorem profile27 : Upper (D (n:=5) [2,3,17,17,24]) (R (n:=5) [2,3,17,17,24]) [] 2 := profile27_node0

def profile28_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node0 : Upper (D (n:=5) [2,4,9,16,32]) (R (n:=5) [2,4,9,16,32]) [] 2 := by
  apply routed_branch (D (n:=5) [2,4,9,16,32]) (R (n:=5) [2,4,9,16,32]) [] 2 (by decide) (choices 0) [] profile28_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,4,9,16,32]) (R (n:=5) [2,4,9,16,32]) [] (choices 0) [] profile28_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile28 : Upper (D (n:=5) [2,4,9,16,32]) (R (n:=5) [2,4,9,16,32]) [] 2 := profile28_node0

def profile29_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node0 : Upper (D (n:=5) [2,4,9,24,24]) (R (n:=5) [2,4,9,24,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,4,9,24,24]) (R (n:=5) [2,4,9,24,24]) [] 2 (by decide) (choices 0) [] profile29_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,4,9,24,24]) (R (n:=5) [2,4,9,24,24]) [] (choices 0) [] profile29_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile29 : Upper (D (n:=5) [2,4,9,24,24]) (R (n:=5) [2,4,9,24,24]) [] 2 := profile29_node0

def profile30_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node0 : Upper (D (n:=5) [2,4,16,16,25]) (R (n:=5) [2,4,16,16,25]) [] 2 := by
  apply routed_branch (D (n:=5) [2,4,16,16,25]) (R (n:=5) [2,4,16,16,25]) [] 2 (by decide) (choices 0) [] profile30_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,4,16,16,25]) (R (n:=5) [2,4,16,16,25]) [] (choices 0) [] profile30_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile30 : Upper (D (n:=5) [2,4,16,16,25]) (R (n:=5) [2,4,16,16,25]) [] 2 := profile30_node0

def profile31_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node0 : Upper (D (n:=5) [2,4,16,17,24]) (R (n:=5) [2,4,16,17,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,4,16,17,24]) (R (n:=5) [2,4,16,17,24]) [] 2 (by decide) (choices 0) [] profile31_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,4,16,17,24]) (R (n:=5) [2,4,16,17,24]) [] (choices 0) [] profile31_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile31 : Upper (D (n:=5) [2,4,16,17,24]) (R (n:=5) [2,4,16,17,24]) [] 2 := profile31_node0

def profile32_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 31 31 31 31 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile32_node0 : Upper (D (n:=5) [2,9,9,9,34]) (R (n:=5) [2,9,9,9,34]) [] 2 :=
  bound_sound (D (n:=5) [2,9,9,9,34]) (R (n:=5) [2,9,9,9,34]) [] 2 profile32_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,9,34]) (R (n:=5) [2,9,9,9,34]) [] 2 profile32_node0_cert).mp (by decide +kernel))

theorem profile32 : Upper (D (n:=5) [2,9,9,9,34]) (R (n:=5) [2,9,9,9,34]) [] 2 := profile32_node0

def profile33_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 31 31 31 31 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile33_node0 : Upper (D (n:=5) [2,9,9,10,33]) (R (n:=5) [2,9,9,10,33]) [] 2 :=
  bound_sound (D (n:=5) [2,9,9,10,33]) (R (n:=5) [2,9,9,10,33]) [] 2 profile33_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,10,33]) (R (n:=5) [2,9,9,10,33]) [] 2 profile33_node0_cert).mp (by decide +kernel))

theorem profile33 : Upper (D (n:=5) [2,9,9,10,33]) (R (n:=5) [2,9,9,10,33]) [] 2 := profile33_node0

def profile34_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 15 15 15 15 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile34_node0 : Upper (D (n:=5) [2,9,9,11,32]) (R (n:=5) [2,9,9,11,32]) [] 2 :=
  bound_sound (D (n:=5) [2,9,9,11,32]) (R (n:=5) [2,9,9,11,32]) [] 2 profile34_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,11,32]) (R (n:=5) [2,9,9,11,32]) [] 2 profile34_node0_cert).mp (by decide +kernel))

theorem profile34 : Upper (D (n:=5) [2,9,9,11,32]) (R (n:=5) [2,9,9,11,32]) [] 2 := profile34_node0

def profile35_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 18 20 25 23), lower := (rows 1 18 20 25 16), losses := [] }

theorem profile35_node4 : Upper (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0,16,16,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0,16,16,17] 2 profile35_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0,16,16,17] 2 profile35_node4_cert).mp (by decide +kernel))

def profile35_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node3 : Upper (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0,16,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0,16,16] 2 (by decide) (choices 2) [17] profile35_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0,16,16] (choices 2) [17] profile35_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node4

def profile35_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node2 : Upper (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0,16] 2 (by decide) (choices 1) [16] profile35_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0,16] (choices 1) [16] profile35_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node3

def profile35_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node1 : Upper (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0] 2 (by decide) (choices 1) [16] profile35_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [0] (choices 1) [16] profile35_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node2

def profile35_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node0 : Upper (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [] 2 (by decide) (choices 0) [0] profile35_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [] (choices 0) [0] profile35_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node1

theorem profile35 : Upper (D (n:=5) [2,9,9,16,27]) (R (n:=5) [2,9,9,16,27]) [] 2 := profile35_node0

def profile36_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 3 20 25 30), lower := (rows 1 3 20 25 16), losses := [] }

theorem profile36_node4 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16,17] 2 profile36_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16,17] 2 profile36_node4_cert).mp (by decide +kernel))

def profile36_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 20 26 29), lower := (rows 1 3 20 26 16), losses := [] }

theorem profile36_node5 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16,18] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16,18] 2 profile36_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16,18] 2 profile36_node5_cert).mp (by decide +kernel))

def profile36_node6_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 20 28 27), lower := (rows 1 3 20 28 16), losses := [] }

theorem profile36_node6 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16,20] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16,20] 2 profile36_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16,20] 2 profile36_node6_cert).mp (by decide +kernel))

def profile36_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node3 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16] 2 (by decide) (choices 2) [17,18,20] profile36_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1,16] (choices 2) [17,18,20] profile36_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile36_node4
  · exact profile36_node5
  · exact profile36_node6

def profile36_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node2 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1] 2 (by decide) (choices 1) [16] profile36_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,1] (choices 1) [16] profile36_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node3

def profile36_node9_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 6 20 25 27), lower := (rows 1 6 20 25 16), losses := [] }

theorem profile36_node9 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,4,16,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,4,16,17] 2 profile36_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,4,16,17] 2 profile36_node9_cert).mp (by decide +kernel))

def profile36_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node8 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,4,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,4,16] 2 (by decide) (choices 2) [17] profile36_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,4,16] (choices 2) [17] profile36_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node9

def profile36_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node7 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,4] 2 (by decide) (choices 1) [16] profile36_node7_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,4] (choices 1) [16] profile36_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node8

def profile36_node12_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 10 20 25 23), lower := (rows 1 10 20 25 16), losses := [] }

theorem profile36_node12 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,8,16,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,8,16,17] 2 profile36_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,8,16,17] 2 profile36_node12_cert).mp (by decide +kernel))

def profile36_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node11 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,8,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,8,16] 2 (by decide) (choices 2) [17] profile36_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,8,16] (choices 2) [17] profile36_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node12

def profile36_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node10 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,8] 2 (by decide) (choices 1) [16] profile36_node10_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,8] (choices 1) [16] profile36_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node11

def profile36_node15_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 18 5 25 30), lower := (rows 1 18 5 25 16), losses := [] }

theorem profile36_node15 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1,17] 2 profile36_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1,17] 2 profile36_node15_cert).mp (by decide +kernel))

def profile36_node16_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 18 5 26 29), lower := (rows 1 18 5 26 16), losses := [] }

theorem profile36_node16 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1,18] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1,18] 2 profile36_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1,18] 2 profile36_node16_cert).mp (by decide +kernel))

def profile36_node17_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 18 5 28 27), lower := (rows 1 18 5 28 16), losses := [] }

theorem profile36_node17 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1,20] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1,20] 2 profile36_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1,20] 2 profile36_node17_cert).mp (by decide +kernel))

def profile36_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node14 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1] 2 (by decide) (choices 2) [17,18,20] profile36_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,1] (choices 2) [17,18,20] profile36_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile36_node15
  · exact profile36_node16
  · exact profile36_node17

def profile36_node19_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 18 6 25 29), lower := (rows 1 18 6 25 16), losses := [] }

theorem profile36_node19 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,2,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,2,17] 2 profile36_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,2,17] 2 profile36_node19_cert).mp (by decide +kernel))

def profile36_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node18 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,2] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,2] 2 (by decide) (choices 2) [17] profile36_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,2] (choices 2) [17] profile36_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node19

def profile36_node21_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 18 12 25 23), lower := (rows 1 18 12 25 16), losses := [] }

theorem profile36_node21 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,8,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,8,17] 2 profile36_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,8,17] 2 profile36_node21_cert).mp (by decide +kernel))

def profile36_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node20 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,8] 2 (by decide) (choices 2) [17] profile36_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,8] (choices 2) [17] profile36_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node21

def profile36_node23_cert : Bound 5 := { allowed := (rows 0 0 0 16 1), upper := (rows 1 18 20 11 29), lower := (rows 1 18 20 11 16), losses := [] }

theorem profile36_node23 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,16,3] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,16,3] 2 profile36_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,16,3] 2 profile36_node23_cert).mp (by decide +kernel))

def profile36_node24_cert : Bound 5 := { allowed := (rows 0 0 0 16 1), upper := (rows 1 18 20 13 27), lower := (rows 1 18 20 13 16), losses := [] }

theorem profile36_node24 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,16,5] 2 :=
  bound_sound (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,16,5] 2 profile36_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,16,5] 2 profile36_node24_cert).mp (by decide +kernel))

def profile36_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node22 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,16] 2 (by decide) (choices 2) [3,5] profile36_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16,16] (choices 2) [3,5] profile36_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile36_node23
  · exact profile36_node24

def profile36_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node13 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16] 2 (by decide) (choices 1) [1,2,8,16] profile36_node13_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0,16] (choices 1) [1,2,8,16] profile36_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile36_node14
  · exact profile36_node18
  · exact profile36_node20
  · exact profile36_node22

def profile36_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node1 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0] 2 (by decide) (choices 1) [1,4,8,16] profile36_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [0] (choices 1) [1,4,8,16] profile36_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile36_node2
  · exact profile36_node7
  · exact profile36_node10
  · exact profile36_node13

def profile36_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node0 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [] 2 (by decide) (choices 0) [0] profile36_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [] (choices 0) [0] profile36_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node1

theorem profile36 : Upper (D (n:=5) [2,9,9,17,26]) (R (n:=5) [2,9,9,17,26]) [] 2 := profile36_node0

def profile37_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 3 12 25 30), lower := (rows 1 3 12 25 16), losses := [] }

theorem profile37_node4 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,17] 2 profile37_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,17] 2 profile37_node4_cert).mp (by decide +kernel))

def profile37_node6_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 3 12 26 29), lower := (rows 1 3 12 26 29), losses := [] }

theorem profile37_node6 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,18,13] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,18,13] 2 profile37_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,18,13] 2 profile37_node6_cert).mp (by decide +kernel))

def profile37_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node5 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,18] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,18] 2 (by decide) (choices 3) [13] profile37_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,18] (choices 3) [13] profile37_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node6

def profile37_node7_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 3 12 28 27), lower := (rows 1 3 12 28 16), losses := [{ target := 0, region := (rows 0 2 28 24 16), good := (rows 0 2 12 28 28) }] }

theorem profile37_node7 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,20] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,20] 2 profile37_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8,20] 2 profile37_node7_cert).mp (by decide +kernel))

def profile37_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node3 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8] 2 (by decide) (choices 2) [17,18,20] profile37_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1,8] (choices 2) [17,18,20] profile37_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node4
  · exact profile37_node5
  · exact profile37_node7

def profile37_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node2 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1] 2 (by decide) (choices 1) [8] profile37_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,1] (choices 1) [8] profile37_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node3

def profile37_node10_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 6 12 25 27), lower := (rows 1 6 12 25 16), losses := [] }

theorem profile37_node10 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,4,8,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,4,8,17] 2 profile37_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,4,8,17] 2 profile37_node10_cert).mp (by decide +kernel))

def profile37_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node9 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,4,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,4,8] 2 (by decide) (choices 2) [17] profile37_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,4,8] (choices 2) [17] profile37_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node10

def profile37_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node8 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,4] 2 (by decide) (choices 1) [8] profile37_node8_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,4] (choices 1) [8] profile37_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node9

def profile37_node13_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 5 25 30), lower := (rows 1 10 5 25 16), losses := [] }

theorem profile37_node13 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,17] 2 profile37_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,17] 2 profile37_node13_cert).mp (by decide +kernel))

def profile37_node14_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 5 26 29), lower := (rows 1 10 5 26 16), losses := [{ target := 0, region := (rows 0 26 4 24 16), good := (rows 0 10 4 26 26) }] }

theorem profile37_node14 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,18] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,18] 2 profile37_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,18] 2 profile37_node14_cert).mp (by decide +kernel))

def profile37_node16_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 10 5 28 27), lower := (rows 1 10 5 28 27), losses := [] }

theorem profile37_node16 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,20,11] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,20,11] 2 profile37_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,20,11] 2 profile37_node16_cert).mp (by decide +kernel))

def profile37_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node15 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,20] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,20] 2 (by decide) (choices 3) [11] profile37_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1,20] (choices 3) [11] profile37_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node16

def profile37_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node12 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1] 2 (by decide) (choices 2) [17,18,20] profile37_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,1] (choices 2) [17,18,20] profile37_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node13
  · exact profile37_node14
  · exact profile37_node15

def profile37_node18_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 6 25 29), lower := (rows 1 10 6 25 16), losses := [] }

theorem profile37_node18 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,2,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,2,17] 2 profile37_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,2,17] 2 profile37_node18_cert).mp (by decide +kernel))

def profile37_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node17 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,2] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,2] 2 (by decide) (choices 2) [17] profile37_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,2] (choices 2) [17] profile37_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node18

def profile37_node20_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 12 25 23), lower := (rows 1 10 12 25 16), losses := [] }

theorem profile37_node20 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,8,17] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,8,17] 2 profile37_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,8,17] 2 profile37_node20_cert).mp (by decide +kernel))

def profile37_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node19 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,8] 2 (by decide) (choices 2) [17] profile37_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,8] (choices 2) [17] profile37_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node20

def profile37_node22_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 20 11 29), lower := (rows 1 10 20 11 16), losses := [] }

theorem profile37_node22 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,16,3] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,16,3] 2 profile37_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,16,3] 2 profile37_node22_cert).mp (by decide +kernel))

def profile37_node23_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 20 13 27), lower := (rows 1 10 20 13 16), losses := [] }

theorem profile37_node23 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,16,5] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,16,5] 2 profile37_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,16,5] 2 profile37_node23_cert).mp (by decide +kernel))

def profile37_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node21 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,16] 2 (by decide) (choices 2) [3,5] profile37_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8,16] (choices 2) [3,5] profile37_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile37_node22
  · exact profile37_node23

def profile37_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node11 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8] 2 (by decide) (choices 1) [1,2,8,16] profile37_node11_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,8] (choices 1) [1,2,8,16] profile37_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile37_node12
  · exact profile37_node17
  · exact profile37_node19
  · exact profile37_node21

def profile37_node26_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 18 12 11 29), lower := (rows 1 18 12 11 16), losses := [] }

theorem profile37_node26 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16,8,3] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16,8,3] 2 profile37_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16,8,3] 2 profile37_node26_cert).mp (by decide +kernel))

def profile37_node27_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 18 12 13 27), lower := (rows 1 18 12 13 16), losses := [] }

theorem profile37_node27 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16,8,5] 2 :=
  bound_sound (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16,8,5] 2 profile37_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16,8,5] 2 profile37_node27_cert).mp (by decide +kernel))

def profile37_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node25 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16,8] 2 (by decide) (choices 2) [3,5] profile37_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16,8] (choices 2) [3,5] profile37_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile37_node26
  · exact profile37_node27

def profile37_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node24 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16] 2 (by decide) (choices 1) [8] profile37_node24_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0,16] (choices 1) [8] profile37_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node25

def profile37_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node1 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0] 2 (by decide) (choices 1) [1,4,8,16] profile37_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [0] (choices 1) [1,4,8,16] profile37_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile37_node2
  · exact profile37_node8
  · exact profile37_node11
  · exact profile37_node24

def profile37_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node0 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [] 2 (by decide) (choices 0) [0] profile37_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [] (choices 0) [0] profile37_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node1

theorem profile37 : Upper (D (n:=5) [2,9,9,18,25]) (R (n:=5) [2,9,9,18,25]) [] 2 := profile37_node0

def profile38_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 12 11 29), lower := (rows 1 10 12 11 16), losses := [] }

theorem profile38_node4 : Upper (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8,8,3] 2 :=
  bound_sound (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8,8,3] 2 profile38_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8,8,3] 2 profile38_node4_cert).mp (by decide +kernel))

def profile38_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 12 13 27), lower := (rows 1 10 12 13 16), losses := [] }

theorem profile38_node5 : Upper (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8,8,5] 2 :=
  bound_sound (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8,8,5] 2 profile38_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8,8,5] 2 profile38_node5_cert).mp (by decide +kernel))

def profile38_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node3 : Upper (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8,8] 2 (by decide) (choices 2) [3,5] profile38_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8,8] (choices 2) [3,5] profile38_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile38_node4
  · exact profile38_node5

def profile38_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node2 : Upper (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8] 2 (by decide) (choices 1) [8] profile38_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0,8] (choices 1) [8] profile38_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node3

def profile38_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node1 : Upper (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0] 2 (by decide) (choices 1) [8] profile38_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [0] (choices 1) [8] profile38_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node2

def profile38_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node0 : Upper (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [] 2 (by decide) (choices 0) [0] profile38_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [] (choices 0) [0] profile38_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node1

theorem profile38 : Upper (D (n:=5) [2,9,9,19,24]) (R (n:=5) [2,9,9,19,24]) [] 2 := profile38_node0

def profile39_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 0), upper := (rows 1 3 12 12 31), lower := (rows 1 3 12 12 31), losses := [] }

theorem profile39_node5 : Upper (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1,8,4,15] 2 :=
  bound_sound (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1,8,4,15] 2 profile39_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1,8,4,15] 2 profile39_node5_cert).mp (by decide +kernel))

def profile39_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node4 : Upper (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1,8,4] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1,8,4] 2 (by decide) (choices 4) [15] profile39_node4_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1,8,4] (choices 4) [15] profile39_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node5

def profile39_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node3 : Upper (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1,8] 2 (by decide) (choices 1) [4] profile39_node3_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1,8] (choices 1) [4] profile39_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node4

def profile39_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node2 : Upper (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1] 2 (by decide) (choices 1) [8] profile39_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,1] (choices 1) [8] profile39_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node3

def profile39_node9_cert : Bound 5 := { allowed := (rows 0 0 0 0 0), upper := (rows 1 6 12 9 31), lower := (rows 1 6 12 9 31), losses := [] }

theorem profile39_node9 : Upper (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4,8,1,15] 2 :=
  bound_sound (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4,8,1,15] 2 profile39_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4,8,1,15] 2 profile39_node9_cert).mp (by decide +kernel))

def profile39_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node8 : Upper (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4,8,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4,8,1] 2 (by decide) (choices 4) [15] profile39_node8_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4,8,1] (choices 4) [15] profile39_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node9

def profile39_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node7 : Upper (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4,8] 2 (by decide) (choices 1) [1] profile39_node7_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4,8] (choices 1) [1] profile39_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node8

def profile39_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node6 : Upper (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4] 2 (by decide) (choices 1) [8] profile39_node6_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0,4] (choices 1) [8] profile39_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node7

def profile39_node1_route : Route 5 := (fun mask => match mask with | 8 => (4,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile39_node1 : Upper (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0] 2 (by decide) (choices 1) [1,4] profile39_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [0] (choices 1) [1,4] profile39_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile39_node2
  · exact profile39_node6

def profile39_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node0 : Upper (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [] 2 (by decide) (choices 0) [0] profile39_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [] (choices 0) [0] profile39_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node1

theorem profile39 : Upper (D (n:=5) [2,9,10,10,32]) (R (n:=5) [2,9,10,10,32]) [] 2 := profile39_node0

def profile40_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 3 20 28 23), lower := (rows 1 3 20 28 16), losses := [{ target := 0, region := (rows 0 2 28 28 16), good := (rows 0 2 28 28 28) }] }

theorem profile40_node4 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,1,16,20] 2 :=
  bound_sound (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,1,16,20] 2 profile40_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,1,16,20] 2 profile40_node4_cert).mp (by decide +kernel))

def profile40_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node3 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,1,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,1,16] 2 (by decide) (choices 2) [20] profile40_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,1,16] (choices 2) [20] profile40_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node4

def profile40_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node2 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,1] 2 (by decide) (choices 1) [16] profile40_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,1] (choices 1) [16] profile40_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node3

def profile40_node7_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 20 25 23), lower := (rows 1 6 20 25 16), losses := [{ target := 2, region := (rows 31 2 0 28 16), good := (rows 1 11 25 25 25) }] }

theorem profile40_node7 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,4,16,17] 2 :=
  bound_sound (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,4,16,17] 2 profile40_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,4,16,17] 2 profile40_node7_cert).mp (by decide +kernel))

def profile40_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node6 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,4,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,4,16] 2 (by decide) (choices 2) [17] profile40_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,4,16] (choices 2) [17] profile40_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node7

def profile40_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node5 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,4] 2 (by decide) (choices 1) [16] profile40_node5_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,4] (choices 1) [16] profile40_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node6

def profile40_node11_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 18 5 28 23), lower := (rows 1 18 5 28 23), losses := [] }

theorem profile40_node11 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,1,20,7] 2 :=
  bound_sound (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,1,20,7] 2 profile40_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,1,20,7] 2 profile40_node11_cert).mp (by decide +kernel))

def profile40_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node10 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,1,20] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,1,20] 2 (by decide) (choices 3) [7] profile40_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,1,20] (choices 3) [7] profile40_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node11

def profile40_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node9 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,1] 2 (by decide) (choices 2) [20] profile40_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,1] (choices 2) [20] profile40_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node10

def profile40_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node12 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,2] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,2] 2 (by decide) (choices 2) [] profile40_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,2] (choices 2) [] profile40_node12_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile40_node14_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 18 20 13 23), lower := (rows 1 18 20 13 16), losses := [{ target := 4, region := (rows 31 2 4 12 0), good := (rows 1 3 13 13 1) }] }

theorem profile40_node14 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,16,5] 2 :=
  bound_sound (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,16,5] 2 profile40_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,16,5] 2 profile40_node14_cert).mp (by decide +kernel))

def profile40_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node13 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,16] 2 (by decide) (choices 2) [5] profile40_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16,16] (choices 2) [5] profile40_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node14

def profile40_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node8 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16] 2 (by decide) (choices 1) [1,2,16] profile40_node8_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0,16] (choices 1) [1,2,16] profile40_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node9
  · exact profile40_node12
  · exact profile40_node13

def profile40_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node1 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0] 2 (by decide) (choices 1) [1,4,16] profile40_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [0] (choices 1) [1,4,16] profile40_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node2
  · exact profile40_node5
  · exact profile40_node8

def profile40_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node0 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [] 2 (by decide) (choices 0) [0] profile40_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [] (choices 0) [0] profile40_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node1

theorem profile40 : Upper (D (n:=5) [2,9,10,16,26]) (R (n:=5) [2,9,10,16,26]) [] 2 := profile40_node0

def profile41_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 5 28 30), lower := (rows 1 3 5 28 30), losses := [] }

theorem profile41_node5 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,1,20,14] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,1,20,14] 2 profile41_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,1,20,14] 2 profile41_node5_cert).mp (by decide +kernel))

def profile41_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node4 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,1,20] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,1,20] 2 (by decide) (choices 3) [14] profile41_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,1,20] (choices 3) [14] profile41_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node5

def profile41_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node3 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,1] 2 (by decide) (choices 2) [20] profile41_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,1] (choices 2) [20] profile41_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node4

def profile41_node8_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 3 6 28 29), lower := (rows 1 3 6 28 29), losses := [] }

theorem profile41_node8 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,2,20,13] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,2,20,13] 2 profile41_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,2,20,13] 2 profile41_node8_cert).mp (by decide +kernel))

def profile41_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node7 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,2,20] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,2,20] 2 (by decide) (choices 3) [13] profile41_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,2,20] (choices 3) [13] profile41_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node8

def profile41_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node6 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,2] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,2] 2 (by decide) (choices 2) [20] profile41_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,2] (choices 2) [20] profile41_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node7

def profile41_node10_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 3 12 28 23), lower := (rows 1 3 12 28 16), losses := [{ target := 0, region := (rows 0 2 28 24 16), good := (rows 0 2 12 28 28) }] }

theorem profile41_node10 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,8,20] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,8,20] 2 profile41_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,8,20] 2 profile41_node10_cert).mp (by decide +kernel))

def profile41_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node9 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,8] 2 (by decide) (choices 2) [20] profile41_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,8] (choices 2) [20] profile41_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node10

def profile41_node12_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 3 20 13 30), lower := (rows 1 3 20 13 16), losses := [] }

theorem profile41_node12 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16,5] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16,5] 2 profile41_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16,5] 2 profile41_node12_cert).mp (by decide +kernel))

def profile41_node14_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 3 20 14 29), lower := (rows 1 3 20 14 29), losses := [] }

theorem profile41_node14 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16,6,13] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16,6,13] 2 profile41_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16,6,13] 2 profile41_node14_cert).mp (by decide +kernel))

def profile41_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node13 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16,6] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16,6] 2 (by decide) (choices 3) [13] profile41_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16,6] (choices 3) [13] profile41_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node14

def profile41_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node11 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16] 2 (by decide) (choices 2) [5,6] profile41_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1,16] (choices 2) [5,6] profile41_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node12
  · exact profile41_node13

def profile41_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node2 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1] 2 (by decide) (choices 1) [1,2,8,16] profile41_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,1] (choices 1) [1,2,8,16] profile41_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node3
  · exact profile41_node6
  · exact profile41_node9
  · exact profile41_node11

def profile41_node17_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 5 25 30), lower := (rows 1 6 5 25 16), losses := [{ target := 2, region := (rows 31 2 0 24 16), good := (rows 1 3 1 25 25) }] }

theorem profile41_node17 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,17] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,17] 2 profile41_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,17] 2 profile41_node17_cert).mp (by decide +kernel))

def profile41_node19_cert : Bound 5 := { allowed := (rows 0 0 0 5 0), upper := (rows 1 6 5 26 29), lower := (rows 1 6 5 26 29), losses := [] }

theorem profile41_node19 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,18,13] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,18,13] 2 profile41_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,18,13] 2 profile41_node19_cert).mp (by decide +kernel))

def profile41_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node18 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,18] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,18] 2 (by decide) (choices 3) [13] profile41_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,18] (choices 3) [13] profile41_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node19

def profile41_node21_cert : Bound 5 := { allowed := (rows 0 0 0 1 4), upper := (rows 1 6 5 28 27), lower := (rows 1 6 5 28 27), losses := [] }

theorem profile41_node21 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,20,11] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,20,11] 2 profile41_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,20,11] 2 profile41_node21_cert).mp (by decide +kernel))

def profile41_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node20 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,20] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,20] 2 (by decide) (choices 3) [11] profile41_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1,20] (choices 3) [11] profile41_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node21

def profile41_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node16 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1] 2 (by decide) (choices 2) [17,18,20] profile41_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,1] (choices 2) [17,18,20] profile41_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile41_node17
  · exact profile41_node18
  · exact profile41_node20

def profile41_node23_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 6 25 29), lower := (rows 1 6 6 25 16), losses := [{ target := 2, region := (rows 31 2 0 24 16), good := (rows 1 3 3 25 25) }] }

theorem profile41_node23 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,2,17] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,2,17] 2 profile41_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,2,17] 2 profile41_node23_cert).mp (by decide +kernel))

def profile41_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node22 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,2] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,2] 2 (by decide) (choices 2) [17] profile41_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,2] (choices 2) [17] profile41_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node23

def profile41_node25_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 12 25 23), lower := (rows 1 6 12 25 16), losses := [{ target := 2, region := (rows 31 2 0 24 16), good := (rows 1 3 9 25 25) }] }

theorem profile41_node25 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,8,17] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,8,17] 2 profile41_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,8,17] 2 profile41_node25_cert).mp (by decide +kernel))

def profile41_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node24 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,8] 2 (by decide) (choices 2) [17] profile41_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,8] (choices 2) [17] profile41_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node25

def profile41_node27_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 20 11 29), lower := (rows 1 6 20 11 16), losses := [{ target := 2, region := (rows 31 2 0 10 16), good := (rows 1 11 17 11 17) }] }

theorem profile41_node27 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,16,3] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,16,3] 2 profile41_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,16,3] 2 profile41_node27_cert).mp (by decide +kernel))

def profile41_node28_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 20 13 27), lower := (rows 1 6 20 13 16), losses := [] }

theorem profile41_node28 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,16,5] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,16,5] 2 profile41_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,16,5] 2 profile41_node28_cert).mp (by decide +kernel))

def profile41_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node26 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,16] 2 (by decide) (choices 2) [3,5] profile41_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4,16] (choices 2) [3,5] profile41_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node27
  · exact profile41_node28

def profile41_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node15 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4] 2 (by decide) (choices 1) [1,2,8,16] profile41_node15_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,4] (choices 1) [1,2,8,16] profile41_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node16
  · exact profile41_node22
  · exact profile41_node24
  · exact profile41_node26

def profile41_node32_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 10 5 28 23), lower := (rows 1 10 5 28 23), losses := [] }

theorem profile41_node32 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,1,20,7] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,1,20,7] 2 profile41_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,1,20,7] 2 profile41_node32_cert).mp (by decide +kernel))

def profile41_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node31 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,1,20] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,1,20] 2 (by decide) (choices 3) [7] profile41_node31_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,1,20] (choices 3) [7] profile41_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node32

def profile41_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node30 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,1] 2 (by decide) (choices 2) [20] profile41_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,1] (choices 2) [20] profile41_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node31

def profile41_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node33 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,2] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,2] 2 (by decide) (choices 2) [] profile41_node33_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,2] (choices 2) [] profile41_node33_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile41_node35_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 10 20 13 23), lower := (rows 1 10 20 13 16), losses := [] }

theorem profile41_node35 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,16,5] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,16,5] 2 profile41_node35_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,16,5] 2 profile41_node35_cert).mp (by decide +kernel))

def profile41_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node34 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,16] 2 (by decide) (choices 2) [5] profile41_node34_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8,16] (choices 2) [5] profile41_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node35

def profile41_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node29 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8] 2 (by decide) (choices 1) [1,2,16] profile41_node29_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,8] (choices 1) [1,2,16] profile41_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile41_node30
  · exact profile41_node33
  · exact profile41_node34

def profile41_node38_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 18 5 13 30), lower := (rows 1 18 5 13 16), losses := [] }

theorem profile41_node38 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1,5] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1,5] 2 profile41_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1,5] 2 profile41_node38_cert).mp (by decide +kernel))

def profile41_node40_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 18 5 14 29), lower := (rows 1 18 5 14 29), losses := [] }

theorem profile41_node40 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1,6,13] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1,6,13] 2 profile41_node40_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1,6,13] 2 profile41_node40_cert).mp (by decide +kernel))

def profile41_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node39 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1,6] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1,6] 2 (by decide) (choices 3) [13] profile41_node39_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1,6] (choices 3) [13] profile41_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node40

def profile41_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node37 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1] 2 (by decide) (choices 2) [5,6] profile41_node37_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,1] (choices 2) [5,6] profile41_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node38
  · exact profile41_node39

def profile41_node42_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 18 6 13 29), lower := (rows 1 18 6 13 16), losses := [] }

theorem profile41_node42 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,2,5] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,2,5] 2 profile41_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,2,5] 2 profile41_node42_cert).mp (by decide +kernel))

def profile41_node41_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node41 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,2] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,2] 2 (by decide) (choices 2) [5] profile41_node41_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,2] (choices 2) [5] profile41_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node42

def profile41_node44_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 18 12 13 23), lower := (rows 1 18 12 13 16), losses := [] }

theorem profile41_node44 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,8,5] 2 :=
  bound_sound (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,8,5] 2 profile41_node44_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,8,5] 2 profile41_node44_cert).mp (by decide +kernel))

def profile41_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node43 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,8] 2 (by decide) (choices 2) [5] profile41_node43_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16,8] (choices 2) [5] profile41_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node44

def profile41_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node36 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16] 2 (by decide) (choices 1) [1,2,8] profile41_node36_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0,16] (choices 1) [1,2,8] profile41_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile41_node37
  · exact profile41_node41
  · exact profile41_node43

def profile41_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node1 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0] 2 (by decide) (choices 1) [1,4,8,16] profile41_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [0] (choices 1) [1,4,8,16] profile41_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node2
  · exact profile41_node15
  · exact profile41_node29
  · exact profile41_node36

def profile41_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node0 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [] 2 (by decide) (choices 0) [0] profile41_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [] (choices 0) [0] profile41_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node1

theorem profile41 : Upper (D (n:=5) [2,9,10,17,25]) (R (n:=5) [2,9,10,17,25]) [] 2 := profile41_node0

def profile42_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 3 12 13 30), lower := (rows 1 3 12 13 30), losses := [] }

theorem profile42_node5 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,5,14] 2 :=
  bound_sound (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,5,14] 2 profile42_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,5,14] 2 profile42_node5_cert).mp (by decide +kernel))

def profile42_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node4 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,5] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,5] 2 (by decide) (choices 3) [14] profile42_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,5] (choices 3) [14] profile42_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node5

def profile42_node7_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 3 12 14 29), lower := (rows 1 3 12 14 29), losses := [] }

theorem profile42_node7 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,6,13] 2 :=
  bound_sound (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,6,13] 2 profile42_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,6,13] 2 profile42_node7_cert).mp (by decide +kernel))

def profile42_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node6 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,6] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,6] 2 (by decide) (choices 3) [13] profile42_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8,6] (choices 3) [13] profile42_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node7

def profile42_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node3 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8] 2 (by decide) (choices 2) [5,6] profile42_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1,8] (choices 2) [5,6] profile42_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile42_node4
  · exact profile42_node6

def profile42_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node2 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1] 2 (by decide) (choices 1) [8] profile42_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,1] (choices 1) [8] profile42_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node3

def profile42_node11_cert : Bound 5 := { allowed := (rows 0 0 0 4 0), upper := (rows 1 6 12 11 29), lower := (rows 1 6 12 11 29), losses := [] }

theorem profile42_node11 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,3,13] 2 :=
  bound_sound (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,3,13] 2 profile42_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,3,13] 2 profile42_node11_cert).mp (by decide +kernel))

def profile42_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node10 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,3] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,3] 2 (by decide) (choices 3) [13] profile42_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,3] (choices 3) [13] profile42_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node11

def profile42_node13_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 1 6 12 13 27), lower := (rows 1 6 12 13 27), losses := [] }

theorem profile42_node13 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,5,11] 2 :=
  bound_sound (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,5,11] 2 profile42_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,5,11] 2 profile42_node13_cert).mp (by decide +kernel))

def profile42_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node12 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,5] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,5] 2 (by decide) (choices 3) [11] profile42_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8,5] (choices 3) [11] profile42_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node13

def profile42_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node9 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8] 2 (by decide) (choices 2) [3,5] profile42_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4,8] (choices 2) [3,5] profile42_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile42_node10
  · exact profile42_node12

def profile42_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node8 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4] 2 (by decide) (choices 1) [8] profile42_node8_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,4] (choices 1) [8] profile42_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node9

def profile42_node16_cert : Bound 5 := { allowed := (rows 0 0 0 0 12), upper := (rows 1 10 5 13 30), lower := (rows 1 10 5 13 16), losses := [{ target := 0, region := (rows 0 10 4 8 24), good := (rows 0 26 4 30 16) }] }

theorem profile42_node16 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1,5] 2 :=
  bound_sound (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1,5] 2 profile42_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1,5] 2 profile42_node16_cert).mp (by decide +kernel))

def profile42_node18_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 10 5 14 29), lower := (rows 1 10 5 14 29), losses := [] }

theorem profile42_node18 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1,6,13] 2 :=
  bound_sound (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1,6,13] 2 profile42_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1,6,13] 2 profile42_node18_cert).mp (by decide +kernel))

def profile42_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node17 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1,6] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1,6] 2 (by decide) (choices 3) [13] profile42_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1,6] (choices 3) [13] profile42_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node18

def profile42_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node15 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1] 2 (by decide) (choices 2) [5,6] profile42_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,1] (choices 2) [5,6] profile42_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile42_node16
  · exact profile42_node17

def profile42_node21_cert : Bound 5 := { allowed := (rows 0 0 0 0 0), upper := (rows 1 10 6 13 29), lower := (rows 1 10 6 13 29), losses := [] }

theorem profile42_node21 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,2,5,13] 2 :=
  bound_sound (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,2,5,13] 2 profile42_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,2,5,13] 2 profile42_node21_cert).mp (by decide +kernel))

def profile42_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node20 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,2,5] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,2,5] 2 (by decide) (choices 3) [13] profile42_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,2,5] (choices 3) [13] profile42_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node21

def profile42_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node19 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,2] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,2] 2 (by decide) (choices 2) [5] profile42_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,2] (choices 2) [5] profile42_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node20

def profile42_node24_cert : Bound 5 := { allowed := (rows 0 0 0 0 8), upper := (rows 1 10 12 13 23), lower := (rows 1 10 12 13 23), losses := [] }

theorem profile42_node24 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,8,5,7] 2 :=
  bound_sound (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,8,5,7] 2 profile42_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,8,5,7] 2 profile42_node24_cert).mp (by decide +kernel))

def profile42_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node23 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,8,5] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,8,5] 2 (by decide) (choices 3) [7] profile42_node23_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,8,5] (choices 3) [7] profile42_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node24

def profile42_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node22 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,8] 2 (by decide) (choices 2) [5] profile42_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8,8] (choices 2) [5] profile42_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node23

def profile42_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node14 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8] 2 (by decide) (choices 1) [1,2,8] profile42_node14_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0,8] (choices 1) [1,2,8] profile42_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile42_node15
  · exact profile42_node19
  · exact profile42_node22

def profile42_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node1 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0] 2 (by decide) (choices 1) [1,4,8] profile42_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [0] (choices 1) [1,4,8] profile42_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile42_node2
  · exact profile42_node8
  · exact profile42_node14

def profile42_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node0 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [] 2 (by decide) (choices 0) [0] profile42_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [] (choices 0) [0] profile42_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node1

theorem profile42 : Upper (D (n:=5) [2,9,10,18,24]) (R (n:=5) [2,9,10,18,24]) [] 2 := profile42_node0

def profile43_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 6 5 28 23), lower := (rows 1 6 5 28 23), losses := [] }

theorem profile43_node5 : Upper (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,1,20,7] 2 :=
  bound_sound (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,1,20,7] 2 profile43_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,1,20,7] 2 profile43_node5_cert).mp (by decide +kernel))

def profile43_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node4 : Upper (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,1,20] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,1,20] 2 (by decide) (choices 3) [7] profile43_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,1,20] (choices 3) [7] profile43_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node5

def profile43_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node3 : Upper (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,1] 2 (by decide) (choices 2) [20] profile43_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,1] (choices 2) [20] profile43_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node4

def profile43_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node6 : Upper (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,2] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,2] 2 (by decide) (choices 2) [] profile43_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,2] (choices 2) [] profile43_node6_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile43_node8_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 20 13 23), lower := (rows 1 6 20 13 16), losses := [] }

theorem profile43_node8 : Upper (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,16,5] 2 :=
  bound_sound (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,16,5] 2 profile43_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,16,5] 2 profile43_node8_cert).mp (by decide +kernel))

def profile43_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node7 : Upper (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,16] 2 (by decide) (choices 2) [5] profile43_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4,16] (choices 2) [5] profile43_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node8

def profile43_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node2 : Upper (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4] 2 (by decide) (choices 1) [1,2,16] profile43_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0,4] (choices 1) [1,2,16] profile43_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile43_node3
  · exact profile43_node6
  · exact profile43_node7

def profile43_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node1 : Upper (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0] 2 (by decide) (choices 1) [4] profile43_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [0] (choices 1) [4] profile43_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node2

def profile43_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node0 : Upper (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [] 2 (by decide) (choices 0) [0] profile43_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [] (choices 0) [0] profile43_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node1

theorem profile43 : Upper (D (n:=5) [2,9,11,16,25]) (R (n:=5) [2,9,11,16,25]) [] 2 := profile43_node0

def profile44_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 5 13 30), lower := (rows 1 6 5 13 16), losses := [] }

theorem profile44_node4 : Upper (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,1,5] 2 :=
  bound_sound (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,1,5] 2 profile44_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,1,5] 2 profile44_node4_cert).mp (by decide +kernel))

def profile44_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 5 14 29), lower := (rows 1 6 5 14 16), losses := [{ target := 0, region := (rows 0 14 4 14 16), good := (rows 0 14 14 14 16) }] }

theorem profile44_node5 : Upper (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,1,6] 2 :=
  bound_sound (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,1,6] 2 profile44_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,1,6] 2 profile44_node5_cert).mp (by decide +kernel))

def profile44_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node3 : Upper (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,1] 2 (by decide) (choices 2) [5,6] profile44_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,1] (choices 2) [5,6] profile44_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile44_node4
  · exact profile44_node5

def profile44_node7_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 6 13 29), lower := (rows 1 6 6 13 16), losses := [] }

theorem profile44_node7 : Upper (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,2,5] 2 :=
  bound_sound (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,2,5] 2 profile44_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,2,5] 2 profile44_node7_cert).mp (by decide +kernel))

def profile44_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node6 : Upper (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,2] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,2] 2 (by decide) (choices 2) [5] profile44_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,2] (choices 2) [5] profile44_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile44_node7

def profile44_node9_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 12 13 23), lower := (rows 1 6 12 13 16), losses := [] }

theorem profile44_node9 : Upper (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,8,5] 2 :=
  bound_sound (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,8,5] 2 profile44_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,8,5] 2 profile44_node9_cert).mp (by decide +kernel))

def profile44_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node8 : Upper (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,8] 2 (by decide) (choices 2) [5] profile44_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4,8] (choices 2) [5] profile44_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile44_node9

def profile44_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node2 : Upper (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4] 2 (by decide) (choices 1) [1,2,8] profile44_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0,4] (choices 1) [1,2,8] profile44_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile44_node3
  · exact profile44_node6
  · exact profile44_node8

def profile44_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node1 : Upper (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0] 2 (by decide) (choices 1) [4] profile44_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [0] (choices 1) [4] profile44_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile44_node2

def profile44_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node0 : Upper (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [] 2 (by decide) (choices 0) [0] profile44_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [] (choices 0) [0] profile44_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile44_node1

theorem profile44 : Upper (D (n:=5) [2,9,11,17,24]) (R (n:=5) [2,9,11,17,24]) [] 2 := profile44_node0

def profile45_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node0 : Upper (D (n:=5) [2,9,12,16,24]) (R (n:=5) [2,9,12,16,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,12,16,24]) (R (n:=5) [2,9,12,16,24]) [] 2 (by decide) (choices 0) [] profile45_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,12,16,24]) (R (n:=5) [2,9,12,16,24]) [] (choices 0) [] profile45_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile45 : Upper (D (n:=5) [2,9,12,16,24]) (R (n:=5) [2,9,12,16,24]) [] 2 := profile45_node0

def profile46_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile46_node0 : Upper (D (n:=5) [2,9,16,16,20]) (R (n:=5) [2,9,16,16,20]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,16,20]) (R (n:=5) [2,9,16,16,20]) [] 2 (by decide) (choices 0) [] profile46_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,16,20]) (R (n:=5) [2,9,16,16,20]) [] (choices 0) [] profile46_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile46 : Upper (D (n:=5) [2,9,16,16,20]) (R (n:=5) [2,9,16,16,20]) [] 2 := profile46_node0

def profile47_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 18 21 25 26), lower := (rows 1 18 21 25 16), losses := [] }

theorem profile47_node4 : Upper (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,17,17] 2 :=
  bound_sound (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,17,17] 2 profile47_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,17,17] 2 profile47_node4_cert).mp (by decide +kernel))

def profile47_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 18 21 26 25), lower := (rows 1 18 21 26 16), losses := [] }

theorem profile47_node5 : Upper (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,17,18] 2 :=
  bound_sound (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,17,18] 2 profile47_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,17,18] 2 profile47_node5_cert).mp (by decide +kernel))

def profile47_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node3 : Upper (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,17] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,17] 2 (by decide) (choices 2) [17,18] profile47_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,17] (choices 2) [17,18] profile47_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile47_node4
  · exact profile47_node5

def profile47_node7_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 18 22 25 25), lower := (rows 1 18 22 25 16), losses := [] }

theorem profile47_node7 : Upper (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,18,17] 2 :=
  bound_sound (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,18,17] 2 profile47_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,18,17] 2 profile47_node7_cert).mp (by decide +kernel))

def profile47_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node6 : Upper (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,18] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,18] 2 (by decide) (choices 2) [17] profile47_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,18] (choices 2) [17] profile47_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile47_node7

def profile47_node9_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 18 28 25 19), lower := (rows 1 18 28 25 16), losses := [] }

theorem profile47_node9 : Upper (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,24,17] 2 :=
  bound_sound (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,24,17] 2 profile47_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,24,17] 2 profile47_node9_cert).mp (by decide +kernel))

def profile47_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node8 : Upper (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,24] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,24] 2 (by decide) (choices 2) [17] profile47_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16,24] (choices 2) [17] profile47_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile47_node9

def profile47_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node2 : Upper (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16] 2 (by decide) (choices 2) [17,18,24] profile47_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0,16] (choices 2) [17,18,24] profile47_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile47_node3
  · exact profile47_node6
  · exact profile47_node8

def profile47_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node1 : Upper (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0] 2 (by decide) (choices 1) [16] profile47_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [0] (choices 1) [16] profile47_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile47_node2

def profile47_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node0 : Upper (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [] 2 (by decide) (choices 0) [0] profile47_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [] (choices 0) [0] profile47_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile47_node1

theorem profile47 : Upper (D (n:=5) [2,9,16,17,19]) (R (n:=5) [2,9,16,17,19]) [] 2 := profile47_node0

def profile48_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 3 28 25 26), lower := (rows 1 3 28 25 16), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 0 2 28 28 16) }] }

theorem profile48_node4 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24,17] 2 :=
  bound_sound (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24,17] 2 profile48_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24,17] 2 profile48_node4_cert).mp (by decide +kernel))

def profile48_node6_cert : Bound 5 := { allowed := (rows 0 0 1 1 0), upper := (rows 1 3 28 26 25), lower := (rows 1 3 28 26 25), losses := [] }

theorem profile48_node6 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24,18,9] 2 :=
  bound_sound (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24,18,9] 2 profile48_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24,18,9] 2 profile48_node6_cert).mp (by decide +kernel))

def profile48_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node5 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24,18] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24,18] 2 (by decide) (choices 2) [9] profile48_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24,18] (choices 2) [9] profile48_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node6

def profile48_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node3 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24] 2 (by decide) (choices 2) [17,18] profile48_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1,24] (choices 2) [17,18] profile48_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile48_node4
  · exact profile48_node5

def profile48_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node2 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1] 2 (by decide) (choices 2) [24] profile48_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,1] (choices 2) [24] profile48_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node3

def profile48_node9_cert : Bound 5 := { allowed := (rows 0 0 8 0 8), upper := (rows 1 10 21 25 26), lower := (rows 1 10 21 25 16), losses := [{ target := 0, region := (rows 0 10 4 8 26), good := (rows 0 26 20 26 16) }] }

theorem profile48_node9 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,17,17] 2 :=
  bound_sound (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,17,17] 2 profile48_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,17,17] 2 profile48_node9_cert).mp (by decide +kernel))

def profile48_node10_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 21 26 25), lower := (rows 1 10 21 26 16), losses := [{ target := 0, region := (rows 0 30 4 28 16), good := (rows 0 10 30 26 26) },{ target := 3, region := (rows 31 2 28 0 16), good := (rows 1 7 21 23 21) }] }

theorem profile48_node10 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,17,18] 2 :=
  bound_sound (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,17,18] 2 profile48_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,17,18] 2 profile48_node10_cert).mp (by decide +kernel))

def profile48_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node8 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,17] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,17] 2 (by decide) (choices 2) [17,18] profile48_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,17] (choices 2) [17,18] profile48_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile48_node9
  · exact profile48_node10

def profile48_node13_cert : Bound 5 := { allowed := (rows 0 0 9 0 0), upper := (rows 1 10 22 25 25), lower := (rows 1 10 22 25 25), losses := [] }

theorem profile48_node13 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,18,17,9] 2 :=
  bound_sound (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,18,17,9] 2 profile48_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,18,17,9] 2 profile48_node13_cert).mp (by decide +kernel))

def profile48_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node12 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,18,17] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,18,17] 2 (by decide) (choices 2) [9] profile48_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,18,17] (choices 2) [9] profile48_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node13

def profile48_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node11 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,18] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,18] 2 (by decide) (choices 2) [17] profile48_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,18] (choices 2) [17] profile48_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node12

def profile48_node15_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 28 25 19), lower := (rows 1 10 28 25 16), losses := [{ target := 0, region := (rows 0 14 12 8 16), good := (rows 0 14 30 30 16) }] }

theorem profile48_node15 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,24,17] 2 :=
  bound_sound (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,24,17] 2 profile48_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,24,17] 2 profile48_node15_cert).mp (by decide +kernel))

def profile48_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node14 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,24] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,24] 2 (by decide) (choices 2) [17] profile48_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8,24] (choices 2) [17] profile48_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node15

def profile48_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node7 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8] 2 (by decide) (choices 2) [17,18,24] profile48_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0,8] (choices 2) [17,18,24] profile48_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile48_node8
  · exact profile48_node11
  · exact profile48_node14

def profile48_node1_route : Route 5 := (fun mask => match mask with | 16 => (8,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile48_node1 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0] 2 (by decide) (choices 1) [1,8] profile48_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [0] (choices 1) [1,8] profile48_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile48_node2
  · exact profile48_node7

def profile48_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node0 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [] 2 (by decide) (choices 0) [0] profile48_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [] (choices 0) [0] profile48_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node1

theorem profile48 : Upper (D (n:=5) [2,9,16,18,18]) (R (n:=5) [2,9,16,18,18]) [] 2 := profile48_node0

def profile49_node4_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 21 26 28), lower := (rows 1 3 21 26 16), losses := [] }

theorem profile49_node4 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,17,18] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,17,18] 2 profile49_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,17,18] 2 profile49_node4_cert).mp (by decide +kernel))

def profile49_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 21 28 26), lower := (rows 1 3 21 28 16), losses := [] }

theorem profile49_node5 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,17,20] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,17,20] 2 profile49_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,17,20] 2 profile49_node5_cert).mp (by decide +kernel))

def profile49_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node3 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,17] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,17] 2 (by decide) (choices 2) [18,20] profile49_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,17] (choices 2) [18,20] profile49_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile49_node4
  · exact profile49_node5

def profile49_node7_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 3 22 25 28), lower := (rows 1 3 22 25 16), losses := [] }

theorem profile49_node7 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,18,17] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,18,17] 2 profile49_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,18,17] 2 profile49_node7_cert).mp (by decide +kernel))

def profile49_node8_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 3 22 28 25), lower := (rows 1 3 22 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 0 2 30 28 16) }] }

theorem profile49_node8 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,18,20] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,18,20] 2 profile49_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,18,20] 2 profile49_node8_cert).mp (by decide +kernel))

def profile49_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node6 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,18] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,18] 2 (by decide) (choices 2) [17,20] profile49_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,18] (choices 2) [17,20] profile49_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile49_node7
  · exact profile49_node8

def profile49_node10_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 3 28 25 22), lower := (rows 1 3 28 25 16), losses := [] }

theorem profile49_node10 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24,17] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24,17] 2 profile49_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24,17] 2 profile49_node10_cert).mp (by decide +kernel))

def profile49_node11_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 28 26 21), lower := (rows 1 3 28 26 16), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 0 2 28 30 16) }] }

theorem profile49_node11 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24,18] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24,18] 2 profile49_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24,18] 2 profile49_node11_cert).mp (by decide +kernel))

def profile49_node12_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 3 28 28 19), lower := (rows 1 3 28 28 16), losses := [{ target := 0, region := (rows 0 2 28 28 16), good := (rows 0 2 28 28 28) }] }

theorem profile49_node12 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24,20] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24,20] 2 profile49_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24,20] 2 profile49_node12_cert).mp (by decide +kernel))

def profile49_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node9 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24] 2 (by decide) (choices 2) [17,18,20] profile49_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1,24] (choices 2) [17,18,20] profile49_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile49_node10
  · exact profile49_node11
  · exact profile49_node12

def profile49_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node2 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1] 2 (by decide) (choices 2) [17,18,24] profile49_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,1] (choices 2) [17,18,24] profile49_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile49_node3
  · exact profile49_node6
  · exact profile49_node9

def profile49_node15_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 6 21 25 26), lower := (rows 1 6 21 25 16), losses := [] }

theorem profile49_node15 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,17,17] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,17,17] 2 profile49_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,17,17] 2 profile49_node15_cert).mp (by decide +kernel))

def profile49_node16_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 6 21 26 25), lower := (rows 1 6 21 26 16), losses := [] }

theorem profile49_node16 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,17,18] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,17,18] 2 profile49_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,17,18] 2 profile49_node16_cert).mp (by decide +kernel))

def profile49_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node14 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,17] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,17] 2 (by decide) (choices 2) [17,18] profile49_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,17] (choices 2) [17,18] profile49_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile49_node15
  · exact profile49_node16

def profile49_node18_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 6 22 25 25), lower := (rows 1 6 22 25 16), losses := [] }

theorem profile49_node18 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,18,17] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,18,17] 2 profile49_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,18,17] 2 profile49_node18_cert).mp (by decide +kernel))

def profile49_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node17 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,18] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,18] 2 (by decide) (choices 2) [17] profile49_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,18] (choices 2) [17] profile49_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node18

def profile49_node20_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 6 28 25 19), lower := (rows 1 6 28 25 16), losses := [] }

theorem profile49_node20 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,24,17] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,24,17] 2 profile49_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,24,17] 2 profile49_node20_cert).mp (by decide +kernel))

def profile49_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node19 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,24] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,24] 2 (by decide) (choices 2) [17] profile49_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4,24] (choices 2) [17] profile49_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node20

def profile49_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node13 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4] 2 (by decide) (choices 2) [17,18,24] profile49_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,4] (choices 2) [17,18,24] profile49_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile49_node14
  · exact profile49_node17
  · exact profile49_node19

def profile49_node23_cert : Bound 5 := { allowed := (rows 0 0 16 0 1), upper := (rows 1 18 7 25 28), lower := (rows 1 18 7 25 16), losses := [] }

theorem profile49_node23 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,3,17] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,3,17] 2 profile49_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,3,17] 2 profile49_node23_cert).mp (by decide +kernel))

def profile49_node24_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 18 7 28 25), lower := (rows 1 18 7 28 16), losses := [{ target := 4, region := (rows 31 2 6 8 0), good := (rows 1 7 7 13 1) }] }

theorem profile49_node24 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,3,20] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,3,20] 2 profile49_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,3,20] 2 profile49_node24_cert).mp (by decide +kernel))

def profile49_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node22 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,3] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,3] 2 (by decide) (choices 2) [17,20] profile49_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,3] (choices 2) [17,20] profile49_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile49_node23
  · exact profile49_node24

def profile49_node26_cert : Bound 5 := { allowed := (rows 0 0 16 0 1), upper := (rows 1 18 13 25 22), lower := (rows 1 18 13 25 16), losses := [] }

theorem profile49_node26 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9,17] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9,17] 2 profile49_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9,17] 2 profile49_node26_cert).mp (by decide +kernel))

def profile49_node27_cert : Bound 5 := { allowed := (rows 0 0 16 0 1), upper := (rows 1 18 13 26 21), lower := (rows 1 18 13 26 16), losses := [{ target := 0, region := (rows 0 26 4 26 16), good := (rows 0 26 14 26 26) }] }

theorem profile49_node27 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9,18] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9,18] 2 profile49_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9,18] 2 profile49_node27_cert).mp (by decide +kernel))

def profile49_node28_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 18 13 28 19), lower := (rows 1 18 13 28 16), losses := [{ target := 4, region := (rows 31 2 12 8 0), good := (rows 1 3 13 13 1) }] }

theorem profile49_node28 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9,20] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9,20] 2 profile49_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9,20] 2 profile49_node28_cert).mp (by decide +kernel))

def profile49_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node25 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9] 2 (by decide) (choices 2) [17,18,20] profile49_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,9] (choices 2) [17,18,20] profile49_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile49_node26
  · exact profile49_node27
  · exact profile49_node28

def profile49_node30_cert : Bound 5 := { allowed := (rows 0 0 16 0 1), upper := (rows 1 18 14 25 21), lower := (rows 1 18 14 25 16), losses := [{ target := 0, region := (rows 0 26 12 8 16), good := (rows 0 18 14 30 18) }] }

theorem profile49_node30 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,10,17] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,10,17] 2 profile49_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,10,17] 2 profile49_node30_cert).mp (by decide +kernel))

def profile49_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node29 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,10] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,10] 2 (by decide) (choices 2) [17] profile49_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,10] (choices 2) [17] profile49_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node30

def profile49_node32_cert : Bound 5 := { allowed := (rows 0 0 0 16 1), upper := (rows 1 18 21 11 28), lower := (rows 1 18 21 11 16), losses := [] }

theorem profile49_node32 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17,3] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17,3] 2 profile49_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17,3] 2 profile49_node32_cert).mp (by decide +kernel))

def profile49_node33_cert : Bound 5 := { allowed := (rows 0 0 0 16 1), upper := (rows 1 18 21 13 26), lower := (rows 1 18 21 13 16), losses := [] }

theorem profile49_node33 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17,5] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17,5] 2 profile49_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17,5] 2 profile49_node33_cert).mp (by decide +kernel))

def profile49_node34_cert : Bound 5 := { allowed := (rows 0 0 0 16 1), upper := (rows 1 18 21 14 25), lower := (rows 1 18 21 14 16), losses := [{ target := 0, region := (rows 0 22 4 12 16), good := (rows 0 18 30 14 18) }] }

theorem profile49_node34 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17,6] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17,6] 2 profile49_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17,6] 2 profile49_node34_cert).mp (by decide +kernel))

def profile49_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node31 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17] 2 (by decide) (choices 2) [3,5,6] profile49_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,17] (choices 2) [3,5,6] profile49_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile49_node32
  · exact profile49_node33
  · exact profile49_node34

def profile49_node35_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 18 22 13 29), lower := (rows 1 18 22 8 16), losses := [{ target := 0, region := (rows 0 22 22 8 16), good := (rows 0 22 22 8 22) },{ target := 4, region := (rows 31 2 4 12 0), good := (rows 1 3 15 9 1) }] }

theorem profile49_node35 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,18] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,18] 2 profile49_node35_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,18] 2 profile49_node35_cert).mp (by decide +kernel))

def profile49_node37_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 18 28 11 21), lower := (rows 1 18 28 11 16), losses := [{ target := 4, region := (rows 31 2 4 10 0), good := (rows 1 11 13 11 1) }] }

theorem profile49_node37 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,24,3] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,24,3] 2 profile49_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,24,3] 2 profile49_node37_cert).mp (by decide +kernel))

def profile49_node38_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 18 28 13 19), lower := (rows 1 18 28 13 16), losses := [{ target := 4, region := (rows 31 2 4 12 0), good := (rows 1 3 13 13 1) }] }

theorem profile49_node38 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,24,5] 2 :=
  bound_sound (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,24,5] 2 profile49_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,24,5] 2 profile49_node38_cert).mp (by decide +kernel))

def profile49_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node36 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,24] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,24] 2 (by decide) (choices 2) [3,5] profile49_node36_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16,24] (choices 2) [3,5] profile49_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile49_node37
  · exact profile49_node38

def profile49_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node21 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile49_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0,16] (choices 2) [3,9,10,17,18,24] profile49_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile49_node22
  · exact profile49_node25
  · exact profile49_node29
  · exact profile49_node31
  · exact profile49_node35
  · exact profile49_node36

def profile49_node1_route : Route 5 := (fun mask => match mask with | 8 => (4,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile49_node1 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0] 2 (by decide) (choices 1) [1,4,16] profile49_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [0] (choices 1) [1,4,16] profile49_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile49_node2
  · exact profile49_node13
  · exact profile49_node21

def profile49_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node0 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [] 2 := by
  apply routed_branch (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [] 2 (by decide) (choices 0) [0] profile49_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [] (choices 0) [0] profile49_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node1

theorem profile49 : Upper (D (n:=5) [2,9,17,17,18]) (R (n:=5) [2,9,17,17,18]) [] 2 := profile49_node0

def profile50_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node3 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,1] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,1] 2 (by decide) (choices 2) [] profile50_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,1] (choices 2) [] profile50_node3_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile50_node6_cert : Bound 5 := { allowed := (rows 0 0 0 3 0), upper := (rows 1 3 6 28 23), lower := (rows 1 3 6 28 23), losses := [] }

theorem profile50_node6 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,2,20,7] 2 :=
  bound_sound (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,2,20,7] 2 profile50_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,2,20,7] 2 profile50_node6_cert).mp (by decide +kernel))

def profile50_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node5 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,2,20] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,2,20] 2 (by decide) (choices 3) [7] profile50_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,2,20] (choices 3) [7] profile50_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node6

def profile50_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node4 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,2] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,2] 2 (by decide) (choices 2) [20] profile50_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,2] (choices 2) [20] profile50_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node5

def profile50_node9_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 3 20 14 23), lower := (rows 1 3 20 14 23), losses := [] }

theorem profile50_node9 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,16,6,7] 2 :=
  bound_sound (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,16,6,7] 2 profile50_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,16,6,7] 2 profile50_node9_cert).mp (by decide +kernel))

def profile50_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node8 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,16,6] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,16,6] 2 (by decide) (choices 3) [7] profile50_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,16,6] (choices 3) [7] profile50_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node9

def profile50_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node7 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,16] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,16] 2 (by decide) (choices 2) [6] profile50_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1,16] (choices 2) [6] profile50_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node8

def profile50_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node2 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1] 2 (by decide) (choices 1) [1,2,16] profile50_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,1] (choices 1) [1,2,16] profile50_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile50_node3
  · exact profile50_node4
  · exact profile50_node7

def profile50_node13_cert : Bound 5 := { allowed := (rows 0 0 0 5 0), upper := (rows 1 6 5 26 23), lower := (rows 1 6 5 26 23), losses := [] }

theorem profile50_node13 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,1,18,7] 2 :=
  bound_sound (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,1,18,7] 2 profile50_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,1,18,7] 2 profile50_node13_cert).mp (by decide +kernel))

def profile50_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node12 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,1,18] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,1,18] 2 (by decide) (choices 3) [7] profile50_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,1,18] (choices 3) [7] profile50_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node13

def profile50_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node11 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,1] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,1] 2 (by decide) (choices 2) [18] profile50_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,1] (choices 2) [18] profile50_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node12

def profile50_node16_cert : Bound 5 := { allowed := (rows 0 0 0 6 0), upper := (rows 1 6 6 25 23), lower := (rows 1 6 6 25 23), losses := [] }

theorem profile50_node16 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,2,17,7] 2 :=
  bound_sound (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,2,17,7] 2 profile50_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,2,17,7] 2 profile50_node16_cert).mp (by decide +kernel))

def profile50_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node15 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,2,17] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,2,17] 2 (by decide) (choices 3) [7] profile50_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,2,17] (choices 3) [7] profile50_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node16

def profile50_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node14 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,2] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,2] 2 (by decide) (choices 2) [17] profile50_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,2] (choices 2) [17] profile50_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node15

def profile50_node19_cert : Bound 5 := { allowed := (rows 0 0 0 4 0), upper := (rows 1 6 20 11 23), lower := (rows 1 6 20 11 23), losses := [] }

theorem profile50_node19 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,16,3,7] 2 :=
  bound_sound (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,16,3,7] 2 profile50_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,16,3,7] 2 profile50_node19_cert).mp (by decide +kernel))

def profile50_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node18 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,16,3] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,16,3] 2 (by decide) (choices 3) [7] profile50_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,16,3] (choices 3) [7] profile50_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node19

def profile50_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node17 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,16] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,16] 2 (by decide) (choices 2) [3] profile50_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4,16] (choices 2) [3] profile50_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node18

def profile50_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node10 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4] 2 (by decide) (choices 1) [1,2,16] profile50_node10_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,4] (choices 1) [1,2,16] profile50_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile50_node11
  · exact profile50_node14
  · exact profile50_node17

def profile50_node23_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 18 5 14 23), lower := (rows 1 18 5 14 23), losses := [] }

theorem profile50_node23 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,1,6,7] 2 :=
  bound_sound (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,1,6,7] 2 profile50_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,1,6,7] 2 profile50_node23_cert).mp (by decide +kernel))

def profile50_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node22 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,1,6] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,1,6] 2 (by decide) (choices 3) [7] profile50_node22_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,1,6] (choices 3) [7] profile50_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node23

def profile50_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node21 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,1] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,1] 2 (by decide) (choices 2) [6] profile50_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,1] (choices 2) [6] profile50_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node22

def profile50_node26_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 1 18 6 13 23), lower := (rows 1 18 6 13 23), losses := [] }

theorem profile50_node26 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,2,5,7] 2 :=
  bound_sound (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,2,5,7] 2 profile50_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,2,5,7] 2 profile50_node26_cert).mp (by decide +kernel))

def profile50_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node25 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,2,5] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,2,5] 2 (by decide) (choices 3) [7] profile50_node25_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,2,5] (choices 3) [7] profile50_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node26

def profile50_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node24 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,2] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,2] 2 (by decide) (choices 2) [5] profile50_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16,2] (choices 2) [5] profile50_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node25

def profile50_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node20 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16] 2 (by decide) (choices 1) [1,2] profile50_node20_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0,16] (choices 1) [1,2] profile50_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile50_node21
  · exact profile50_node24

def profile50_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node1 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0] 2 (by decide) (choices 1) [1,4,16] profile50_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [0] (choices 1) [1,4,16] profile50_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile50_node2
  · exact profile50_node10
  · exact profile50_node20

def profile50_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node0 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [] 2 (by decide) (choices 0) [0] profile50_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [] (choices 0) [0] profile50_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node1

theorem profile50 : Upper (D (n:=5) [2,10,10,16,25]) (R (n:=5) [2,10,10,16,25]) [] 2 := profile50_node0

def profile51_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 5 14 30), lower := (rows 1 3 5 14 30), losses := [] }

theorem profile51_node5 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,1,6,14] 2 :=
  bound_sound (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,1,6,14] 2 profile51_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,1,6,14] 2 profile51_node5_cert).mp (by decide +kernel))

def profile51_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node4 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,1,6] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,1,6] 2 (by decide) (choices 3) [14] profile51_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,1,6] (choices 3) [14] profile51_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node5

def profile51_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node3 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,1] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,1] 2 (by decide) (choices 2) [6] profile51_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,1] (choices 2) [6] profile51_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node4

def profile51_node8_cert : Bound 5 := { allowed := (rows 0 0 0 2 1), upper := (rows 1 3 6 13 30), lower := (rows 1 3 6 13 30), losses := [] }

theorem profile51_node8 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2,5,14] 2 :=
  bound_sound (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2,5,14] 2 profile51_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2,5,14] 2 profile51_node8_cert).mp (by decide +kernel))

def profile51_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node7 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2,5] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2,5] 2 (by decide) (choices 3) [14] profile51_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2,5] (choices 3) [14] profile51_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node8

def profile51_node9_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 3 6 14 29), lower := (rows 1 3 6 14 16), losses := [{ target := 0, region := (rows 0 2 14 14 16), good := (rows 0 14 14 14 16) },{ target := 1, region := (rows 31 0 4 8 24), good := (rows 1 1 5 29 17) }] }

theorem profile51_node9 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2,6] 2 :=
  bound_sound (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2,6] 2 profile51_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2,6] 2 profile51_node9_cert).mp (by decide +kernel))

def profile51_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node6 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2] 2 (by decide) (choices 2) [5,6] profile51_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,2] (choices 2) [5,6] profile51_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile51_node7
  · exact profile51_node9

def profile51_node12_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 3 12 14 23), lower := (rows 1 3 12 14 23), losses := [] }

theorem profile51_node12 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,8,6,7] 2 :=
  bound_sound (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,8,6,7] 2 profile51_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,8,6,7] 2 profile51_node12_cert).mp (by decide +kernel))

def profile51_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node11 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,8,6] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,8,6] 2 (by decide) (choices 3) [7] profile51_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,8,6] (choices 3) [7] profile51_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node12

def profile51_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node10 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,8] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,8] 2 (by decide) (choices 2) [6] profile51_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1,8] (choices 2) [6] profile51_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node11

def profile51_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node2 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1] 2 (by decide) (choices 1) [1,2,8] profile51_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,1] (choices 1) [1,2,8] profile51_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile51_node3
  · exact profile51_node6
  · exact profile51_node10

def profile51_node16_cert : Bound 5 := { allowed := (rows 0 0 0 4 1), upper := (rows 1 6 5 11 30), lower := (rows 1 6 5 11 30), losses := [] }

theorem profile51_node16 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1,3,14] 2 :=
  bound_sound (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1,3,14] 2 profile51_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1,3,14] 2 profile51_node16_cert).mp (by decide +kernel))

def profile51_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node15 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1,3] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1,3] 2 (by decide) (choices 3) [14] profile51_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1,3] (choices 3) [14] profile51_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node16

def profile51_node17_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 6 5 14 27), lower := (rows 1 6 5 14 16), losses := [{ target := 0, region := (rows 0 14 4 14 16), good := (rows 0 14 14 14 16) },{ target := 2, region := (rows 31 2 0 8 24), good := (rows 1 3 1 27 17) }] }

theorem profile51_node17 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1,6] 2 :=
  bound_sound (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1,6] 2 profile51_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1,6] 2 profile51_node17_cert).mp (by decide +kernel))

def profile51_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node14 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1] 2 (by decide) (choices 2) [3,6] profile51_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,1] (choices 2) [3,6] profile51_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile51_node15
  · exact profile51_node17

def profile51_node20_cert : Bound 5 := { allowed := (rows 0 0 0 4 2), upper := (rows 1 6 6 11 29), lower := (rows 1 6 6 11 29), losses := [] }

theorem profile51_node20 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,3,13] 2 :=
  bound_sound (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,3,13] 2 profile51_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,3,13] 2 profile51_node20_cert).mp (by decide +kernel))

def profile51_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node19 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,3] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,3] 2 (by decide) (choices 3) [13] profile51_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,3] (choices 3) [13] profile51_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node20

def profile51_node22_cert : Bound 5 := { allowed := (rows 0 0 0 2 4), upper := (rows 1 6 6 13 27), lower := (rows 1 6 6 13 27), losses := [] }

theorem profile51_node22 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,5,11] 2 :=
  bound_sound (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,5,11] 2 profile51_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,5,11] 2 profile51_node22_cert).mp (by decide +kernel))

def profile51_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node21 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,5] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,5] 2 (by decide) (choices 3) [11] profile51_node21_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2,5] (choices 3) [11] profile51_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node22

def profile51_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node18 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2] 2 (by decide) (choices 2) [3,5] profile51_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,2] (choices 2) [3,5] profile51_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile51_node19
  · exact profile51_node21

def profile51_node25_cert : Bound 5 := { allowed := (rows 0 0 0 4 0), upper := (rows 1 6 12 11 23), lower := (rows 1 6 12 11 23), losses := [] }

theorem profile51_node25 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,8,3,7] 2 :=
  bound_sound (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,8,3,7] 2 profile51_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,8,3,7] 2 profile51_node25_cert).mp (by decide +kernel))

def profile51_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node24 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,8,3] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,8,3] 2 (by decide) (choices 3) [7] profile51_node24_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,8,3] (choices 3) [7] profile51_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node25

def profile51_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node23 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,8] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,8] 2 (by decide) (choices 2) [3] profile51_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4,8] (choices 2) [3] profile51_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node24

def profile51_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node13 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4] 2 (by decide) (choices 1) [1,2,8] profile51_node13_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,4] (choices 1) [1,2,8] profile51_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile51_node14
  · exact profile51_node18
  · exact profile51_node23

def profile51_node29_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 10 5 14 23), lower := (rows 1 10 5 14 23), losses := [] }

theorem profile51_node29 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,1,6,7] 2 :=
  bound_sound (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,1,6,7] 2 profile51_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,1,6,7] 2 profile51_node29_cert).mp (by decide +kernel))

def profile51_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node28 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,1,6] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,1,6] 2 (by decide) (choices 3) [7] profile51_node28_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,1,6] (choices 3) [7] profile51_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node29

def profile51_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node27 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,1] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,1] 2 (by decide) (choices 2) [6] profile51_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,1] (choices 2) [6] profile51_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node28

def profile51_node32_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 1 10 6 13 23), lower := (rows 1 10 6 13 23), losses := [] }

theorem profile51_node32 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,2,5,7] 2 :=
  bound_sound (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,2,5,7] 2 profile51_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,2,5,7] 2 profile51_node32_cert).mp (by decide +kernel))

def profile51_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node31 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,2,5] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,2,5] 2 (by decide) (choices 3) [7] profile51_node31_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,2,5] (choices 3) [7] profile51_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node32

def profile51_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node30 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,2] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,2] 2 (by decide) (choices 2) [5] profile51_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8,2] (choices 2) [5] profile51_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node31

def profile51_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node26 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8] 2 (by decide) (choices 1) [1,2] profile51_node26_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0,8] (choices 1) [1,2] profile51_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile51_node27
  · exact profile51_node30

def profile51_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node1 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0] 2 (by decide) (choices 1) [1,4,8] profile51_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [0] (choices 1) [1,4,8] profile51_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile51_node2
  · exact profile51_node13
  · exact profile51_node26

def profile51_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node0 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [] 2 (by decide) (choices 0) [0] profile51_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [] (choices 0) [0] profile51_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node1

theorem profile51 : Upper (D (n:=5) [2,10,10,17,24]) (R (n:=5) [2,10,10,17,24]) [] 2 := profile51_node0

def profile52_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 6 5 14 23), lower := (rows 1 6 5 14 23), losses := [] }

theorem profile52_node5 : Upper (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,1,6,7] 2 :=
  bound_sound (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,1,6,7] 2 profile52_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,1,6,7] 2 profile52_node5_cert).mp (by decide +kernel))

def profile52_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node4 : Upper (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,1,6] 2 := by
  apply routed_branch (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,1,6] 2 (by decide) (choices 3) [7] profile52_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,1,6] (choices 3) [7] profile52_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node5

def profile52_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node3 : Upper (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,1] 2 := by
  apply routed_branch (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,1] 2 (by decide) (choices 2) [6] profile52_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,1] (choices 2) [6] profile52_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node4

def profile52_node8_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 1 6 6 13 23), lower := (rows 1 6 6 13 23), losses := [] }

theorem profile52_node8 : Upper (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,2,5,7] 2 :=
  bound_sound (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,2,5,7] 2 profile52_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,2,5,7] 2 profile52_node8_cert).mp (by decide +kernel))

def profile52_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node7 : Upper (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,2,5] 2 := by
  apply routed_branch (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,2,5] 2 (by decide) (choices 3) [7] profile52_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,2,5] (choices 3) [7] profile52_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node8

def profile52_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node6 : Upper (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,2] 2 := by
  apply routed_branch (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,2] 2 (by decide) (choices 2) [5] profile52_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4,2] (choices 2) [5] profile52_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node7

def profile52_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node2 : Upper (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4] 2 (by decide) (choices 1) [1,2] profile52_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0,4] (choices 1) [1,2] profile52_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile52_node3
  · exact profile52_node6

def profile52_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node1 : Upper (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0] 2 (by decide) (choices 1) [4] profile52_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [0] (choices 1) [4] profile52_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node2

def profile52_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node0 : Upper (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [] 2 := by
  apply routed_branch (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [] 2 (by decide) (choices 0) [0] profile52_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [] (choices 0) [0] profile52_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node1

theorem profile52 : Upper (D (n:=5) [2,10,11,16,24]) (R (n:=5) [2,10,11,16,24]) [] 2 := profile52_node0

def profile53_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 18 21 26 19), lower := (rows 1 18 21 26 16), losses := [{ target := 0, region := (rows 0 30 4 30 16), good := (rows 0 26 30 26 26) },{ target := 1, region := (rows 31 0 30 8 16), good := (rows 1 21 21 29 21) }] }

theorem profile53_node4 : Upper (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,17,18] 2 :=
  bound_sound (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,17,18] 2 profile53_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,17,18] 2 profile53_node4_cert).mp (by decide +kernel))

def profile53_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node3 : Upper (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,17] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,17] 2 (by decide) (choices 2) [18] profile53_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,17] (choices 2) [18] profile53_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile53_node4

def profile53_node6_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 18 22 25 19), lower := (rows 1 18 22 25 16), losses := [{ target := 0, region := (rows 0 30 30 8 16), good := (rows 0 22 22 30 22) },{ target := 1, region := (rows 31 0 4 30 16), good := (rows 1 25 29 25 25) }] }

theorem profile53_node6 : Upper (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,18,17] 2 :=
  bound_sound (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,18,17] 2 profile53_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,18,17] 2 profile53_node6_cert).mp (by decide +kernel))

def profile53_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node5 : Upper (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,18] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,18] 2 (by decide) (choices 2) [17] profile53_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16,18] (choices 2) [17] profile53_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile53_node6

def profile53_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node2 : Upper (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16] 2 (by decide) (choices 2) [17,18] profile53_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0,16] (choices 2) [17,18] profile53_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile53_node3
  · exact profile53_node5

def profile53_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node1 : Upper (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0] 2 (by decide) (choices 1) [16] profile53_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [0] (choices 1) [16] profile53_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile53_node2

def profile53_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node0 : Upper (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [] 2 (by decide) (choices 0) [0] profile53_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [] (choices 0) [0] profile53_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile53_node1

theorem profile53 : Upper (D (n:=5) [2,10,16,16,19]) (R (n:=5) [2,10,16,16,19]) [] 2 := profile53_node0

def profile54_node4_cert : Bound 5 := { allowed := (rows 0 0 2 0 2), upper := (rows 1 3 21 26 26), lower := (rows 1 3 21 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 26), good := (rows 0 26 20 26 16) }] }

theorem profile54_node4 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,17,18] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,17,18] 2 profile54_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,17,18] 2 profile54_node4_cert).mp (by decide +kernel))

def profile54_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node3 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,17] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,17] 2 (by decide) (choices 2) [18] profile54_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,17] (choices 2) [18] profile54_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node4

def profile54_node7_cert : Bound 5 := { allowed := (rows 0 0 0 2 1), upper := (rows 1 3 22 25 26), lower := (rows 1 3 22 25 26), losses := [{ target := 0, region := (rows 0 2 20 8 16), good := (rows 0 2 22 28 30) }] }

theorem profile54_node7 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18,17,10] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18,17,10] 2 profile54_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18,17,10] 2 profile54_node7_cert).mp (by decide +kernel))

def profile54_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node6 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18,17] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18,17] 2 (by decide) (choices 2) [10] profile54_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18,17] (choices 2) [10] profile54_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node7

def profile54_node8_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 3 22 26 25), lower := (rows 1 3 22 26 16), losses := [{ target := 0, region := (rows 0 2 12 12 16), good := (rows 0 2 30 30 16) }] }

theorem profile54_node8 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18,18] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18,18] 2 profile54_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18,18] 2 profile54_node8_cert).mp (by decide +kernel))

def profile54_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node5 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18] 2 (by decide) (choices 2) [17,18] profile54_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,18] (choices 2) [17,18] profile54_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile54_node6
  · exact profile54_node8

def profile54_node11_cert : Bound 5 := { allowed := (rows 0 0 2 0 0), upper := (rows 1 3 28 26 19), lower := (rows 1 3 28 26 19), losses := [{ target := 0, region := (rows 0 2 28 24 16), good := (rows 0 2 28 30 30) }] }

theorem profile54_node11 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,24,18,3] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,24,18,3] 2 profile54_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,24,18,3] 2 profile54_node11_cert).mp (by decide +kernel))

def profile54_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node10 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,24,18] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,24,18] 2 (by decide) (choices 2) [3] profile54_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,24,18] (choices 2) [3] profile54_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node11

def profile54_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node9 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,24] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,24] 2 (by decide) (choices 2) [18] profile54_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1,24] (choices 2) [18] profile54_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node10

def profile54_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node2 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1] 2 (by decide) (choices 2) [17,18,24] profile54_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,1] (choices 2) [17,18,24] profile54_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile54_node3
  · exact profile54_node5
  · exact profile54_node9

def profile54_node14_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 10 21 26 19), lower := (rows 1 10 21 26 16), losses := [{ target := 0, region := (rows 0 30 4 28 16), good := (rows 0 10 30 26 26) },{ target := 1, region := (rows 31 0 28 8 16), good := (rows 1 13 21 29 21) }] }

theorem profile54_node14 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,17,18] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,17,18] 2 profile54_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,17,18] 2 profile54_node14_cert).mp (by decide +kernel))

def profile54_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node13 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,17] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,17] 2 (by decide) (choices 2) [18] profile54_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,17] (choices 2) [18] profile54_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node14

def profile54_node16_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 10 22 25 19), lower := (rows 1 10 22 25 16), losses := [{ target := 0, region := (rows 0 10 12 8 16), good := (rows 0 14 22 30 16) },{ target := 1, region := (rows 31 0 4 28 16), good := (rows 1 9 29 25 25) }] }

theorem profile54_node16 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,18,17] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,18,17] 2 profile54_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,18,17] 2 profile54_node16_cert).mp (by decide +kernel))

def profile54_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node15 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,18] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,18] 2 (by decide) (choices 2) [17] profile54_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8,18] (choices 2) [17] profile54_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node16

def profile54_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node12 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8] 2 (by decide) (choices 2) [17,18] profile54_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,8] (choices 2) [17,18] profile54_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile54_node13
  · exact profile54_node15

def profile54_node19_cert : Bound 5 := { allowed := (rows 0 0 16 0 2), upper := (rows 1 18 7 25 26), lower := (rows 1 18 7 25 16), losses := [{ target := 0, region := (rows 0 26 4 8 24), good := (rows 0 18 6 26 18) },{ target := 1, region := (rows 31 0 4 26 16), good := (rows 1 25 13 25 25) }] }

theorem profile54_node19 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,3,17] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,3,17] 2 profile54_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,3,17] 2 profile54_node19_cert).mp (by decide +kernel))

def profile54_node20_cert : Bound 5 := { allowed := (rows 0 0 16 0 1), upper := (rows 1 18 7 26 25), lower := (rows 1 18 7 26 16), losses := [{ target := 0, region := (rows 0 26 4 26 16), good := (rows 0 26 14 26 26) },{ target := 1, region := (rows 31 0 4 8 24), good := (rows 1 17 5 25 17) }] }

theorem profile54_node20 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,3,18] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,3,18] 2 profile54_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,3,18] 2 profile54_node20_cert).mp (by decide +kernel))

def profile54_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node18 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,3] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,3] 2 (by decide) (choices 2) [17,18] profile54_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,3] (choices 2) [17,18] profile54_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile54_node19
  · exact profile54_node20

def profile54_node22_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 18 13 26 19), lower := (rows 1 18 13 26 16), losses := [{ target := 0, region := (rows 0 26 4 26 16), good := (rows 0 26 14 26 26) },{ target := 1, region := (rows 31 0 12 8 16), good := (rows 1 17 13 29 17) },{ target := 4, region := (rows 31 2 12 8 0), good := (rows 1 3 13 15 1) }] }

theorem profile54_node22 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,9,18] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,9,18] 2 profile54_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,9,18] 2 profile54_node22_cert).mp (by decide +kernel))

def profile54_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node21 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,9] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,9] 2 (by decide) (choices 2) [18] profile54_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,9] (choices 2) [18] profile54_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node22

def profile54_node25_cert : Bound 5 := { allowed := (rows 0 0 16 2 0), upper := (rows 1 18 14 25 19), lower := (rows 1 18 14 25 19), losses := [{ target := 0, region := (rows 0 26 12 8 16), good := (rows 0 18 14 30 18) }] }

theorem profile54_node25 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,10,17,3] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,10,17,3] 2 profile54_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,10,17,3] 2 profile54_node25_cert).mp (by decide +kernel))

def profile54_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node24 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,10,17] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,10,17] 2 (by decide) (choices 2) [3] profile54_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,10,17] (choices 2) [3] profile54_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node25

def profile54_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node23 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,10] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,10] 2 (by decide) (choices 2) [17] profile54_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,10] (choices 2) [17] profile54_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node24

def profile54_node27_cert : Bound 5 := { allowed := (rows 0 0 0 16 2), upper := (rows 1 18 21 11 26), lower := (rows 1 18 21 11 16), losses := [{ target := 0, region := (rows 0 30 4 8 24), good := (rows 0 18 22 26 18) },{ target := 1, region := (rows 31 0 22 8 16), good := (rows 1 21 21 13 21) }] }

theorem profile54_node27 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,17,3] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,17,3] 2 profile54_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,17,3] 2 profile54_node27_cert).mp (by decide +kernel))

def profile54_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node26 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,17] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,17] 2 (by decide) (choices 2) [3] profile54_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,17] (choices 2) [3] profile54_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node27

def profile54_node29_cert : Bound 5 := { allowed := (rows 0 0 0 16 1), upper := (rows 1 18 22 11 25), lower := (rows 1 18 22 11 16), losses := [{ target := 0, region := (rows 0 22 22 8 16), good := (rows 0 22 22 14 22) },{ target := 1, region := (rows 31 0 4 8 24), good := (rows 1 17 21 25 17) }] }

theorem profile54_node29 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,18,3] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,18,3] 2 profile54_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,18,3] 2 profile54_node29_cert).mp (by decide +kernel))

def profile54_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node28 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,18] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,18] 2 (by decide) (choices 2) [3] profile54_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,18] (choices 2) [3] profile54_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node29

def profile54_node32_cert : Bound 5 := { allowed := (rows 0 0 3 0 0), upper := (rows 1 18 28 11 19), lower := (rows 1 18 28 11 19), losses := [{ target := 4, region := (rows 31 2 4 26 0), good := (rows 1 11 13 11 11) }] }

theorem profile54_node32 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,24,3,3] 2 :=
  bound_sound (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,24,3,3] 2 profile54_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,24,3,3] 2 profile54_node32_cert).mp (by decide +kernel))

def profile54_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node31 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,24,3] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,24,3] 2 (by decide) (choices 2) [3] profile54_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,24,3] (choices 2) [3] profile54_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node32

def profile54_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node30 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,24] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,24] 2 (by decide) (choices 2) [3] profile54_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16,24] (choices 2) [3] profile54_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node31

def profile54_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node17 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile54_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0,16] (choices 2) [3,9,10,17,18,24] profile54_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile54_node18
  · exact profile54_node21
  · exact profile54_node23
  · exact profile54_node26
  · exact profile54_node28
  · exact profile54_node30

def profile54_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node1 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0] 2 (by decide) (choices 1) [1,8,16] profile54_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [0] (choices 1) [1,8,16] profile54_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile54_node2
  · exact profile54_node12
  · exact profile54_node17

def profile54_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node0 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [] 2 := by
  apply routed_branch (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [] 2 (by decide) (choices 0) [0] profile54_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [] (choices 0) [0] profile54_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node1

theorem profile54 : Upper (D (n:=5) [2,10,16,17,18]) (R (n:=5) [2,10,16,17,18]) [] 2 := profile54_node0

def profile55_node3_cert : Bound 5 := { allowed := (rows 0 0 0 2 2), upper := (rows 1 3 7 30 30), lower := (rows 1 3 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 0 2 30 8 16) }] }

theorem profile55_node3 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,3] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,3] 2 profile55_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,3] 2 profile55_node3_cert).mp (by decide +kernel))

def profile55_node6_cert : Bound 5 := { allowed := (rows 0 0 2 0 1), upper := (rows 1 3 13 26 22), lower := (rows 1 3 13 26 22), losses := [{ target := 0, region := (rows 0 2 4 24 16), good := (rows 0 2 12 26 30) }] }

theorem profile55_node6 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,9,18,6] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,9,18,6] 2 profile55_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,9,18,6] 2 profile55_node6_cert).mp (by decide +kernel))

def profile55_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node5 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,9,18] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,9,18] 2 (by decide) (choices 2) [6] profile55_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,9,18] (choices 2) [6] profile55_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node6

def profile55_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node4 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,9] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,9] 2 (by decide) (choices 2) [18] profile55_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,9] (choices 2) [18] profile55_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node5

def profile55_node8_cert : Bound 5 := { allowed := (rows 0 0 1 0 2), upper := (rows 1 3 14 25 22), lower := (rows 1 3 14 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 0 2 30 24 16) },{ target := 1, region := (rows 31 0 4 24 16), good := (rows 1 1 13 25 25) }] }

theorem profile55_node8 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,17] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,17] 2 profile55_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,17] 2 profile55_node8_cert).mp (by decide +kernel))

def profile55_node9_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 14 26 21), lower := (rows 1 3 14 26 16), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 0 2 14 30 16) },{ target := 1, region := (rows 31 0 4 8 20), good := (rows 1 1 29 25 17) }] }

theorem profile55_node9 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,18] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,18] 2 profile55_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,18] 2 profile55_node9_cert).mp (by decide +kernel))

def profile55_node11_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 1 3 14 28 19), lower := (rows 1 3 14 28 19), losses := [{ target := 0, region := (rows 0 2 20 24 16), good := (rows 0 2 14 28 30) }] }

theorem profile55_node11 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,20,3] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,20,3] 2 profile55_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,20,3] 2 profile55_node11_cert).mp (by decide +kernel))

def profile55_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node10 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,20] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,20] 2 (by decide) (choices 2) [3] profile55_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10,20] (choices 2) [3] profile55_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node11

def profile55_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node7 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10] 2 (by decide) (choices 2) [17,18,20] profile55_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,10] (choices 2) [17,18,20] profile55_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node8
  · exact profile55_node9
  · exact profile55_node10

def profile55_node13_cert : Bound 5 := { allowed := (rows 0 0 2 0 2), upper := (rows 1 3 28 11 22), lower := (rows 1 3 28 11 16), losses := [{ target := 0, region := (rows 0 2 12 8 24), good := (rows 0 2 28 30 16) }] }

theorem profile55_node13 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24,3] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24,3] 2 profile55_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24,3] 2 profile55_node13_cert).mp (by decide +kernel))

def profile55_node15_cert : Bound 5 := { allowed := (rows 0 0 2 0 0), upper := (rows 1 3 28 14 19), lower := (rows 1 3 28 14 19), losses := [{ target := 0, region := (rows 0 2 20 24 16), good := (rows 0 2 28 14 30) }] }

theorem profile55_node15 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24,6,3] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24,6,3] 2 profile55_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24,6,3] 2 profile55_node15_cert).mp (by decide +kernel))

def profile55_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node14 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24,6] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24,6] 2 (by decide) (choices 2) [3] profile55_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24,6] (choices 2) [3] profile55_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node15

def profile55_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node12 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24] 2 (by decide) (choices 2) [3,6] profile55_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1,24] (choices 2) [3,6] profile55_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile55_node13
  · exact profile55_node14

def profile55_node2_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile55_node2 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1] 2 (by decide) (choices 2) [3,9,10,24] profile55_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,1] (choices 2) [3,9,10,24] profile55_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile55_node3
  · exact profile55_node4
  · exact profile55_node7
  · exact profile55_node12

def profile55_node18_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 6 7 25 26), lower := (rows 1 6 7 25 16), losses := [{ target := 1, region := (rows 31 0 4 24 16), good := (rows 1 5 5 25 25) }] }

theorem profile55_node18 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,3,17] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,3,17] 2 profile55_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,3,17] 2 profile55_node18_cert).mp (by decide +kernel))

def profile55_node19_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 6 7 26 25), lower := (rows 1 6 7 26 16), losses := [{ target := 1, region := (rows 31 0 4 8 24), good := (rows 1 5 5 25 17) }] }

theorem profile55_node19 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,3,18] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,3,18] 2 profile55_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,3,18] 2 profile55_node19_cert).mp (by decide +kernel))

def profile55_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node17 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,3] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,3] 2 (by decide) (choices 2) [17,18] profile55_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,3] (choices 2) [17,18] profile55_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile55_node18
  · exact profile55_node19

def profile55_node22_cert : Bound 5 := { allowed := (rows 0 0 2 1 0), upper := (rows 1 6 13 26 19), lower := (rows 1 6 13 26 19), losses := [] }

theorem profile55_node22 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,9,18,3] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,9,18,3] 2 profile55_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,9,18,3] 2 profile55_node22_cert).mp (by decide +kernel))

def profile55_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node21 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,9,18] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,9,18] 2 (by decide) (choices 2) [3] profile55_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,9,18] (choices 2) [3] profile55_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node22

def profile55_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node20 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,9] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,9] 2 (by decide) (choices 2) [18] profile55_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,9] (choices 2) [18] profile55_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node21

def profile55_node24_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 6 14 25 19), lower := (rows 1 6 14 25 16), losses := [{ target := 0, region := (rows 0 14 12 8 16), good := (rows 0 6 14 30 16) },{ target := 1, region := (rows 31 0 4 24 16), good := (rows 1 5 13 25 25) }] }

theorem profile55_node24 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,10,17] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,10,17] 2 profile55_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,10,17] 2 profile55_node24_cert).mp (by decide +kernel))

def profile55_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node23 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,10] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,10] 2 (by decide) (choices 2) [17] profile55_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,10] (choices 2) [17] profile55_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node24

def profile55_node27_cert : Bound 5 := { allowed := (rows 0 0 3 0 0), upper := (rows 1 6 28 11 19), lower := (rows 1 6 28 11 19), losses := [] }

theorem profile55_node27 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,24,3,3] 2 :=
  bound_sound (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,24,3,3] 2 profile55_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,24,3,3] 2 profile55_node27_cert).mp (by decide +kernel))

def profile55_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node26 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,24,3] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,24,3] 2 (by decide) (choices 2) [3] profile55_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,24,3] (choices 2) [3] profile55_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node27

def profile55_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node25 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,24] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,24] 2 (by decide) (choices 2) [3] profile55_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4,24] (choices 2) [3] profile55_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node26

def profile55_node16_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile55_node16 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4] 2 (by decide) (choices 2) [3,9,10,24] profile55_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0,4] (choices 2) [3,9,10,24] profile55_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile55_node17
  · exact profile55_node20
  · exact profile55_node23
  · exact profile55_node25

def profile55_node1_route : Route 5 := (fun mask => match mask with | 8 => (4,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 16 => (4,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile55_node1 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0] 2 (by decide) (choices 1) [1,4] profile55_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [0] (choices 1) [1,4] profile55_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile55_node2
  · exact profile55_node16

def profile55_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node0 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [] 2 := by
  apply routed_branch (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [] 2 (by decide) (choices 0) [0] profile55_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [] (choices 0) [0] profile55_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node1

theorem profile55 : Upper (D (n:=5) [2,10,17,17,17]) (R (n:=5) [2,10,17,17,17]) [] 2 := profile55_node0

def profile56_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 3 22 26 19), lower := (rows 1 3 22 26 16), losses := [{ target := 0, region := (rows 0 2 12 12 16), good := (rows 0 2 30 30 16) }] }

theorem profile56_node4 : Upper (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,1,18,18] 2 :=
  bound_sound (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,1,18,18] 2 profile56_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,1,18,18] 2 profile56_node4_cert).mp (by decide +kernel))

def profile56_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node3 : Upper (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,1,18] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,1,18] 2 (by decide) (choices 2) [18] profile56_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,1,18] (choices 2) [18] profile56_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile56_node4

def profile56_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node2 : Upper (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,1] 2 (by decide) (choices 2) [18] profile56_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,1] (choices 2) [18] profile56_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile56_node3

def profile56_node7_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 18 7 26 19), lower := (rows 1 18 7 26 16), losses := [{ target := 0, region := (rows 0 26 4 26 16), good := (rows 0 26 14 26 26) },{ target := 4, region := (rows 31 2 14 8 0), good := (rows 1 7 7 15 1) }] }

theorem profile56_node7 : Upper (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,3,18] 2 :=
  bound_sound (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,3,18] 2 profile56_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,3,18] 2 profile56_node7_cert).mp (by decide +kernel))

def profile56_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node6 : Upper (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,3] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,3] 2 (by decide) (choices 2) [18] profile56_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,3] (choices 2) [18] profile56_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile56_node7

def profile56_node9_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 18 22 11 19), lower := (rows 1 18 22 11 16), losses := [{ target := 0, region := (rows 0 22 22 8 16), good := (rows 0 22 22 14 22) },{ target := 4, region := (rows 31 2 4 14 0), good := (rows 1 11 15 11 1) }] }

theorem profile56_node9 : Upper (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,18,3] 2 :=
  bound_sound (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,18,3] 2 profile56_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,18,3] 2 profile56_node9_cert).mp (by decide +kernel))

def profile56_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node8 : Upper (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,18] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,18] 2 (by decide) (choices 2) [3] profile56_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16,18] (choices 2) [3] profile56_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile56_node9

def profile56_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node5 : Upper (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16] 2 (by decide) (choices 2) [3,18] profile56_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0,16] (choices 2) [3,18] profile56_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile56_node6
  · exact profile56_node8

def profile56_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node1 : Upper (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0] 2 (by decide) (choices 1) [1,16] profile56_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [0] (choices 1) [1,16] profile56_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile56_node2
  · exact profile56_node5

def profile56_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node0 : Upper (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [] 2 (by decide) (choices 0) [0] profile56_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [] (choices 0) [0] profile56_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile56_node1

theorem profile56 : Upper (D (n:=5) [2,11,16,16,18]) (R (n:=5) [2,11,16,16,18]) [] 2 := profile56_node0

def profile57_node3_cert : Bound 5 := { allowed := (rows 0 0 0 2 2), upper := (rows 1 3 7 26 26), lower := (rows 1 3 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 0 26 30 8 16) }] }

theorem profile57_node3 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,3] 2 :=
  bound_sound (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,3] 2 profile57_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,3] 2 profile57_node3_cert).mp (by decide +kernel))

def profile57_node6_cert : Bound 5 := { allowed := (rows 0 0 1 1 0), upper := (rows 1 3 14 26 19), lower := (rows 1 3 14 26 19), losses := [] }

theorem profile57_node6 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,10,18,3] 2 :=
  bound_sound (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,10,18,3] 2 profile57_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,10,18,3] 2 profile57_node6_cert).mp (by decide +kernel))

def profile57_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node5 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,10,18] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,10,18] 2 (by decide) (choices 2) [3] profile57_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,10,18] (choices 2) [3] profile57_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile57_node6

def profile57_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node4 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,10] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,10] 2 (by decide) (choices 2) [18] profile57_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1,10] (choices 2) [18] profile57_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile57_node5

def profile57_node2_route : Route 5 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile57_node2 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1] 2 (by decide) (choices 2) [3,10] profile57_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,1] (choices 2) [3,10] profile57_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile57_node3
  · exact profile57_node4

def profile57_node9_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 10 7 26 19), lower := (rows 1 10 7 26 16), losses := [{ target := 0, region := (rows 0 26 4 24 16), good := (rows 0 10 6 26 26) }] }

theorem profile57_node9 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,3,18] 2 :=
  bound_sound (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,3,18] 2 profile57_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,3,18] 2 profile57_node9_cert).mp (by decide +kernel))

def profile57_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node8 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,3] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,3] 2 (by decide) (choices 2) [18] profile57_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,3] (choices 2) [18] profile57_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile57_node9

def profile57_node12_cert : Bound 5 := { allowed := (rows 0 0 1 0 0), upper := (rows 1 10 22 11 19), lower := (rows 1 10 22 11 19), losses := [] }

theorem profile57_node12 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,18,3,3] 2 :=
  bound_sound (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,18,3,3] 2 profile57_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,18,3,3] 2 profile57_node12_cert).mp (by decide +kernel))

def profile57_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node11 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,18,3] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,18,3] 2 (by decide) (choices 2) [3] profile57_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,18,3] (choices 2) [3] profile57_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile57_node12

def profile57_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node10 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,18] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,18] 2 (by decide) (choices 2) [3] profile57_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8,18] (choices 2) [3] profile57_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile57_node11

def profile57_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node7 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8] 2 (by decide) (choices 2) [3,18] profile57_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0,8] (choices 2) [3,18] profile57_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile57_node8
  · exact profile57_node10

def profile57_node1_route : Route 5 := (fun mask => match mask with | 16 => (8,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile57_node1 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0] 2 (by decide) (choices 1) [1,8] profile57_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [0] (choices 1) [1,8] profile57_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile57_node2
  · exact profile57_node7

def profile57_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node0 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [] 2 := by
  apply routed_branch (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [] 2 (by decide) (choices 0) [0] profile57_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [] (choices 0) [0] profile57_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile57_node1

theorem profile57 : Upper (D (n:=5) [2,11,16,17,17]) (R (n:=5) [2,11,16,17,17]) [] 2 := profile57_node0

def profile58_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile58_node0 : Upper (D (n:=5) [2,12,16,16,17]) (R (n:=5) [2,12,16,16,17]) [] 2 := by
  apply routed_branch (D (n:=5) [2,12,16,16,17]) (R (n:=5) [2,12,16,16,17]) [] 2 (by decide) (choices 0) [] profile58_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [2,12,16,16,17]) (R (n:=5) [2,12,16,16,17]) [] (choices 0) [] profile58_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile58 : Upper (D (n:=5) [2,12,16,16,17]) (R (n:=5) [2,12,16,16,17]) [] 2 := profile58_node0

def profile59_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node2 : Upper (D (n:=5) [3,3,9,16,32]) (R (n:=5) [3,3,9,16,32]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [3,3,9,16,32]) (R (n:=5) [3,3,9,16,32]) [0,0] 2 (by decide) (choices 1) [] profile59_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,9,16,32]) (R (n:=5) [3,3,9,16,32]) [0,0] (choices 1) [] profile59_node2_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile59_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node1 : Upper (D (n:=5) [3,3,9,16,32]) (R (n:=5) [3,3,9,16,32]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,3,9,16,32]) (R (n:=5) [3,3,9,16,32]) [0] 2 (by decide) (choices 0) [0] profile59_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,9,16,32]) (R (n:=5) [3,3,9,16,32]) [0] (choices 0) [0] profile59_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile59_node2

def profile59_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node0 : Upper (D (n:=5) [3,3,9,16,32]) (R (n:=5) [3,3,9,16,32]) [] 2 := by
  apply routed_branch (D (n:=5) [3,3,9,16,32]) (R (n:=5) [3,3,9,16,32]) [] 2 (by decide) (choices 0) [0] profile59_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,9,16,32]) (R (n:=5) [3,3,9,16,32]) [] (choices 0) [0] profile59_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile59_node1

theorem profile59 : Upper (D (n:=5) [3,3,9,16,32]) (R (n:=5) [3,3,9,16,32]) [] 2 := profile59_node0

def profile60_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node2 : Upper (D (n:=5) [3,3,9,24,24]) (R (n:=5) [3,3,9,24,24]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [3,3,9,24,24]) (R (n:=5) [3,3,9,24,24]) [0,0] 2 (by decide) (choices 1) [] profile60_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,9,24,24]) (R (n:=5) [3,3,9,24,24]) [0,0] (choices 1) [] profile60_node2_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile60_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node1 : Upper (D (n:=5) [3,3,9,24,24]) (R (n:=5) [3,3,9,24,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,3,9,24,24]) (R (n:=5) [3,3,9,24,24]) [0] 2 (by decide) (choices 0) [0] profile60_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,9,24,24]) (R (n:=5) [3,3,9,24,24]) [0] (choices 0) [0] profile60_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile60_node2

def profile60_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node0 : Upper (D (n:=5) [3,3,9,24,24]) (R (n:=5) [3,3,9,24,24]) [] 2 := by
  apply routed_branch (D (n:=5) [3,3,9,24,24]) (R (n:=5) [3,3,9,24,24]) [] 2 (by decide) (choices 0) [0] profile60_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,9,24,24]) (R (n:=5) [3,3,9,24,24]) [] (choices 0) [0] profile60_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile60_node1

theorem profile60 : Upper (D (n:=5) [3,3,9,24,24]) (R (n:=5) [3,3,9,24,24]) [] 2 := profile60_node0

def profile61_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node3 : Upper (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [0,0,3] 2 := by
  apply routed_branch (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [0,0,3] 2 (by decide) (choices 2) [] profile61_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [0,0,3] (choices 2) [] profile61_node3_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile61_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node2 : Upper (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [0,0] 2 (by decide) (choices 2) [3] profile61_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [0,0] (choices 2) [3] profile61_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node3

def profile61_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node1 : Upper (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [0] 2 (by decide) (choices 0) [0] profile61_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [0] (choices 0) [0] profile61_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node2

def profile61_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node0 : Upper (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [] 2 := by
  apply routed_branch (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [] 2 (by decide) (choices 0) [0] profile61_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [] (choices 0) [0] profile61_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node1

theorem profile61 : Upper (D (n:=5) [3,3,16,16,25]) (R (n:=5) [3,3,16,16,25]) [] 2 := profile61_node0

def profile62_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 2 7 11 27), lower := (rows 1 2 7 11 16), losses := [] }

theorem profile62_node4 : Upper (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0,0,3,3] 2 :=
  bound_sound (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0,0,3,3] 2 profile62_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0,0,3,3] 2 profile62_node4_cert).mp (by decide +kernel))

def profile62_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile62_node3 : Upper (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0,0,3] 2 := by
  apply routed_branch (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0,0,3] 2 (by decide) (choices 2) [3] profile62_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0,0,3] (choices 2) [3] profile62_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile62_node4

def profile62_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile62_node2 : Upper (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0,0] 2 := by
  apply routed_branch (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0,0] 2 (by decide) (choices 2) [3] profile62_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0,0] (choices 2) [3] profile62_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile62_node3

def profile62_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile62_node1 : Upper (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0] 2 (by decide) (choices 0) [0] profile62_node1_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [0] (choices 0) [0] profile62_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile62_node2

def profile62_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile62_node0 : Upper (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [] 2 := by
  apply routed_branch (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [] 2 (by decide) (choices 0) [0] profile62_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [] (choices 0) [0] profile62_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile62_node1

theorem profile62 : Upper (D (n:=5) [3,3,16,17,24]) (R (n:=5) [3,3,16,17,24]) [] 2 := profile62_node0

def profile63_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile63_node0 : Upper (D (n:=5) [3,4,16,16,24]) (R (n:=5) [3,4,16,16,24]) [] 2 := by
  apply routed_branch (D (n:=5) [3,4,16,16,24]) (R (n:=5) [3,4,16,16,24]) [] 2 (by decide) (choices 0) [] profile63_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,4,16,16,24]) (R (n:=5) [3,4,16,16,24]) [] (choices 0) [] profile63_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile63 : Upper (D (n:=5) [3,4,16,16,24]) (R (n:=5) [3,4,16,16,24]) [] 2 := profile63_node0

def profile64_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 31 31 31 31 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile64_node0 : Upper (D (n:=5) [3,9,9,9,33]) (R (n:=5) [3,9,9,9,33]) [] 2 :=
  bound_sound (D (n:=5) [3,9,9,9,33]) (R (n:=5) [3,9,9,9,33]) [] 2 profile64_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,9,9,33]) (R (n:=5) [3,9,9,9,33]) [] 2 profile64_node0_cert).mp (by decide +kernel))

theorem profile64 : Upper (D (n:=5) [3,9,9,9,33]) (R (n:=5) [3,9,9,9,33]) [] 2 := profile64_node0

def profile65_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 15 15 15 15 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile65_node0 : Upper (D (n:=5) [3,9,9,10,32]) (R (n:=5) [3,9,9,10,32]) [] 2 :=
  bound_sound (D (n:=5) [3,9,9,10,32]) (R (n:=5) [3,9,9,10,32]) [] 2 profile65_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,9,10,32]) (R (n:=5) [3,9,9,10,32]) [] 2 profile65_node0_cert).mp (by decide +kernel))

theorem profile65 : Upper (D (n:=5) [3,9,9,10,32]) (R (n:=5) [3,9,9,10,32]) [] 2 := profile65_node0

def profile66_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 3 20 25 23), lower := (rows 1 3 20 25 16), losses := [] }

theorem profile66_node4 : Upper (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,1,16,17] 2 :=
  bound_sound (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,1,16,17] 2 profile66_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,1,16,17] 2 profile66_node4_cert).mp (by decide +kernel))

def profile66_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node3 : Upper (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,1,16] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,1,16] 2 (by decide) (choices 2) [17] profile66_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,1,16] (choices 2) [17] profile66_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile66_node4

def profile66_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node2 : Upper (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,1] 2 (by decide) (choices 1) [16] profile66_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,1] (choices 1) [16] profile66_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile66_node3

def profile66_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node5 : Upper (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,4] 2 (by decide) (choices 1) [] profile66_node5_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,4] (choices 1) [] profile66_node5_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile66_node8_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 18 5 25 23), lower := (rows 1 18 5 25 16), losses := [] }

theorem profile66_node8 : Upper (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,16,1,17] 2 :=
  bound_sound (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,16,1,17] 2 profile66_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,16,1,17] 2 profile66_node8_cert).mp (by decide +kernel))

def profile66_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node7 : Upper (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,16,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,16,1] 2 (by decide) (choices 2) [17] profile66_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,16,1] (choices 2) [17] profile66_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile66_node8

def profile66_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node6 : Upper (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,16] 2 (by decide) (choices 1) [1] profile66_node6_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0,16] (choices 1) [1] profile66_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile66_node7

def profile66_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node1 : Upper (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0] 2 (by decide) (choices 1) [1,4,16] profile66_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [0] (choices 1) [1,4,16] profile66_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile66_node2
  · exact profile66_node5
  · exact profile66_node6

def profile66_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node0 : Upper (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [] 2 (by decide) (choices 0) [0] profile66_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [] (choices 0) [0] profile66_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile66_node1

theorem profile66 : Upper (D (n:=5) [3,9,9,16,26]) (R (n:=5) [3,9,9,16,26]) [] 2 := profile66_node0

def profile67_node0_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 31 31 31 31 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile67_node0 : Upper (D (n:=5) [3,9,9,17,25]) (R (n:=5) [3,9,9,17,25]) [] 2 :=
  bound_sound (D (n:=5) [3,9,9,17,25]) (R (n:=5) [3,9,9,17,25]) [] 2 profile67_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,9,17,25]) (R (n:=5) [3,9,9,17,25]) [] 2 profile67_node0_cert).mp (by decide +kernel))

theorem profile67 : Upper (D (n:=5) [3,9,9,17,25]) (R (n:=5) [3,9,9,17,25]) [] 2 := profile67_node0

def profile68_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 3 12 11 29), lower := (rows 1 3 12 11 16), losses := [] }

theorem profile68_node4 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1,8,3] 2 :=
  bound_sound (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1,8,3] 2 profile68_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1,8,3] 2 profile68_node4_cert).mp (by decide +kernel))

def profile68_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 3 12 13 27), lower := (rows 1 3 12 13 16), losses := [] }

theorem profile68_node5 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1,8,5] 2 :=
  bound_sound (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1,8,5] 2 profile68_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1,8,5] 2 profile68_node5_cert).mp (by decide +kernel))

def profile68_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node3 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1,8] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1,8] 2 (by decide) (choices 2) [3,5] profile68_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1,8] (choices 2) [3,5] profile68_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile68_node4
  · exact profile68_node5

def profile68_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node2 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1] 2 (by decide) (choices 1) [8] profile68_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,1] (choices 1) [8] profile68_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile68_node3

def profile68_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node6 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,4] 2 (by decide) (choices 1) [] profile68_node6_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,4] (choices 1) [] profile68_node6_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile68_node9_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 5 11 29), lower := (rows 1 10 5 11 16), losses := [] }

theorem profile68_node9 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8,1,3] 2 :=
  bound_sound (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8,1,3] 2 profile68_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8,1,3] 2 profile68_node9_cert).mp (by decide +kernel))

def profile68_node10_cert : Bound 5 := { allowed := (rows 0 0 0 0 9), upper := (rows 1 10 5 13 27), lower := (rows 1 10 5 13 16), losses := [] }

theorem profile68_node10 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8,1,5] 2 :=
  bound_sound (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8,1,5] 2 profile68_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8,1,5] 2 profile68_node10_cert).mp (by decide +kernel))

def profile68_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node8 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8,1] 2 (by decide) (choices 2) [3,5] profile68_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8,1] (choices 2) [3,5] profile68_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile68_node9
  · exact profile68_node10

def profile68_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node7 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8] 2 (by decide) (choices 1) [1] profile68_node7_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0,8] (choices 1) [1] profile68_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile68_node8

def profile68_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node1 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0] 2 (by decide) (choices 1) [1,4,8] profile68_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [0] (choices 1) [1,4,8] profile68_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile68_node2
  · exact profile68_node6
  · exact profile68_node7

def profile68_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node0 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [] 2 := by
  apply routed_branch (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [] 2 (by decide) (choices 0) [0] profile68_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [] (choices 0) [0] profile68_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile68_node1

theorem profile68 : Upper (D (n:=5) [3,9,9,18,24]) (R (n:=5) [3,9,9,18,24]) [] 2 := profile68_node0

def profile69_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 3 5 28 23), lower := (rows 1 3 5 28 23), losses := [] }

theorem profile69_node5 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,1,20,7] 2 :=
  bound_sound (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,1,20,7] 2 profile69_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,1,20,7] 2 profile69_node5_cert).mp (by decide +kernel))

def profile69_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node4 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,1,20] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,1,20] 2 (by decide) (choices 3) [7] profile69_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,1,20] (choices 3) [7] profile69_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node5

def profile69_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node3 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,1] 2 (by decide) (choices 2) [20] profile69_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,1] (choices 2) [20] profile69_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node4

def profile69_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node6 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,2] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,2] 2 (by decide) (choices 2) [] profile69_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,2] (choices 2) [] profile69_node6_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile69_node8_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 3 20 13 23), lower := (rows 1 3 20 13 16), losses := [] }

theorem profile69_node8 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,16,5] 2 :=
  bound_sound (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,16,5] 2 profile69_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,16,5] 2 profile69_node8_cert).mp (by decide +kernel))

def profile69_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node7 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,16] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,16] 2 (by decide) (choices 2) [5] profile69_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1,16] (choices 2) [5] profile69_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node8

def profile69_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node2 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1] 2 (by decide) (choices 1) [1,2,16] profile69_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,1] (choices 1) [1,2,16] profile69_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile69_node3
  · exact profile69_node6
  · exact profile69_node7

def profile69_node11_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 5 25 23), lower := (rows 1 6 5 25 16), losses := [{ target := 2, region := (rows 31 2 0 24 16), good := (rows 1 3 1 25 25) }] }

theorem profile69_node11 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,4,1,17] 2 :=
  bound_sound (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,4,1,17] 2 profile69_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,4,1,17] 2 profile69_node11_cert).mp (by decide +kernel))

def profile69_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node10 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,4,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,4,1] 2 (by decide) (choices 2) [17] profile69_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,4,1] (choices 2) [17] profile69_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node11

def profile69_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node9 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,4] 2 (by decide) (choices 1) [1] profile69_node9_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,4] (choices 1) [1] profile69_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node10

def profile69_node14_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 18 5 13 23), lower := (rows 1 18 5 13 16), losses := [] }

theorem profile69_node14 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,16,1,5] 2 :=
  bound_sound (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,16,1,5] 2 profile69_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,16,1,5] 2 profile69_node14_cert).mp (by decide +kernel))

def profile69_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node13 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,16,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,16,1] 2 (by decide) (choices 2) [5] profile69_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,16,1] (choices 2) [5] profile69_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node14

def profile69_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node12 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,16] 2 (by decide) (choices 1) [1] profile69_node12_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0,16] (choices 1) [1] profile69_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node13

def profile69_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node1 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0] 2 (by decide) (choices 1) [1,4,16] profile69_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [0] (choices 1) [1,4,16] profile69_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile69_node2
  · exact profile69_node9
  · exact profile69_node12

def profile69_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node0 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [] 2 (by decide) (choices 0) [0] profile69_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [] (choices 0) [0] profile69_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node1

theorem profile69 : Upper (D (n:=5) [3,9,10,16,25]) (R (n:=5) [3,9,10,16,25]) [] 2 := profile69_node0

def profile70_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 3 5 13 30), lower := (rows 1 3 5 13 16), losses := [] }

theorem profile70_node4 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1,5] 2 :=
  bound_sound (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1,5] 2 profile70_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1,5] 2 profile70_node4_cert).mp (by decide +kernel))

def profile70_node6_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 3 5 14 29), lower := (rows 1 3 5 14 29), losses := [] }

theorem profile70_node6 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1,6,13] 2 :=
  bound_sound (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1,6,13] 2 profile70_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1,6,13] 2 profile70_node6_cert).mp (by decide +kernel))

def profile70_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node5 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1,6] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1,6] 2 (by decide) (choices 3) [13] profile70_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1,6] (choices 3) [13] profile70_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile70_node6

def profile70_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node3 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1] 2 (by decide) (choices 2) [5,6] profile70_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,1] (choices 2) [5,6] profile70_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile70_node4
  · exact profile70_node5

def profile70_node8_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 3 6 13 29), lower := (rows 1 3 6 13 16), losses := [] }

theorem profile70_node8 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,2,5] 2 :=
  bound_sound (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,2,5] 2 profile70_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,2,5] 2 profile70_node8_cert).mp (by decide +kernel))

def profile70_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node7 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,2] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,2] 2 (by decide) (choices 2) [5] profile70_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,2] (choices 2) [5] profile70_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile70_node8

def profile70_node10_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 3 12 13 23), lower := (rows 1 3 12 13 16), losses := [] }

theorem profile70_node10 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,8,5] 2 :=
  bound_sound (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,8,5] 2 profile70_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,8,5] 2 profile70_node10_cert).mp (by decide +kernel))

def profile70_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node9 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,8] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,8] 2 (by decide) (choices 2) [5] profile70_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1,8] (choices 2) [5] profile70_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile70_node10

def profile70_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node2 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1] 2 (by decide) (choices 1) [1,2,8] profile70_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,1] (choices 1) [1,2,8] profile70_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile70_node3
  · exact profile70_node7
  · exact profile70_node9

def profile70_node13_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 5 11 29), lower := (rows 1 6 5 11 16), losses := [{ target := 2, region := (rows 31 2 0 10 16), good := (rows 1 11 1 11 17) }] }

theorem profile70_node13 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4,1,3] 2 :=
  bound_sound (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4,1,3] 2 profile70_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4,1,3] 2 profile70_node13_cert).mp (by decide +kernel))

def profile70_node14_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 5 13 27), lower := (rows 1 6 5 13 16), losses := [] }

theorem profile70_node14 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4,1,5] 2 :=
  bound_sound (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4,1,5] 2 profile70_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4,1,5] 2 profile70_node14_cert).mp (by decide +kernel))

def profile70_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node12 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4,1] 2 (by decide) (choices 2) [3,5] profile70_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4,1] (choices 2) [3,5] profile70_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile70_node13
  · exact profile70_node14

def profile70_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node11 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4] 2 (by decide) (choices 1) [1] profile70_node11_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,4] (choices 1) [1] profile70_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile70_node12

def profile70_node17_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 10 5 13 23), lower := (rows 1 10 5 13 16), losses := [] }

theorem profile70_node17 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,8,1,5] 2 :=
  bound_sound (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,8,1,5] 2 profile70_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,8,1,5] 2 profile70_node17_cert).mp (by decide +kernel))

def profile70_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node16 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,8,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,8,1] 2 (by decide) (choices 2) [5] profile70_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,8,1] (choices 2) [5] profile70_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile70_node17

def profile70_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node15 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,8] 2 (by decide) (choices 1) [1] profile70_node15_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0,8] (choices 1) [1] profile70_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile70_node16

def profile70_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node1 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0] 2 (by decide) (choices 1) [1,4,8] profile70_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [0] (choices 1) [1,4,8] profile70_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile70_node2
  · exact profile70_node11
  · exact profile70_node15

def profile70_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node0 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [] 2 := by
  apply routed_branch (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [] 2 (by decide) (choices 0) [0] profile70_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [] (choices 0) [0] profile70_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile70_node1

theorem profile70 : Upper (D (n:=5) [3,9,10,17,24]) (R (n:=5) [3,9,10,17,24]) [] 2 := profile70_node0

def profile71_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 6 5 13 23), lower := (rows 1 6 5 13 16), losses := [] }

theorem profile71_node4 : Upper (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0,4,1,5] 2 :=
  bound_sound (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0,4,1,5] 2 profile71_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0,4,1,5] 2 profile71_node4_cert).mp (by decide +kernel))

def profile71_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node3 : Upper (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0,4,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0,4,1] 2 (by decide) (choices 2) [5] profile71_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0,4,1] (choices 2) [5] profile71_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile71_node4

def profile71_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node2 : Upper (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0,4] 2 (by decide) (choices 1) [1] profile71_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0,4] (choices 1) [1] profile71_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile71_node3

def profile71_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node1 : Upper (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0] 2 (by decide) (choices 1) [4] profile71_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [0] (choices 1) [4] profile71_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile71_node2

def profile71_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node0 : Upper (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [] 2 := by
  apply routed_branch (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [] 2 (by decide) (choices 0) [0] profile71_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [] (choices 0) [0] profile71_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile71_node1

theorem profile71 : Upper (D (n:=5) [3,9,11,16,24]) (R (n:=5) [3,9,11,16,24]) [] 2 := profile71_node0

def profile72_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 18 21 25 19), lower := (rows 1 18 21 25 16), losses := [] }

theorem profile72_node4 : Upper (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0,16,17,17] 2 :=
  bound_sound (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0,16,17,17] 2 profile72_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0,16,17,17] 2 profile72_node4_cert).mp (by decide +kernel))

def profile72_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node3 : Upper (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0,16,17] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0,16,17] 2 (by decide) (choices 2) [17] profile72_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0,16,17] (choices 2) [17] profile72_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile72_node4

def profile72_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node2 : Upper (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0,16] 2 (by decide) (choices 2) [17] profile72_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0,16] (choices 2) [17] profile72_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile72_node3

def profile72_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node1 : Upper (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0] 2 (by decide) (choices 1) [16] profile72_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [0] (choices 1) [16] profile72_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile72_node2

def profile72_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node0 : Upper (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [] 2 (by decide) (choices 0) [0] profile72_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [] (choices 0) [0] profile72_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile72_node1

theorem profile72 : Upper (D (n:=5) [3,9,16,16,19]) (R (n:=5) [3,9,16,16,19]) [] 2 := profile72_node0

def profile73_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 3 21 25 26), lower := (rows 1 3 21 25 16), losses := [] }

theorem profile73_node4 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,17,17] 2 :=
  bound_sound (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,17,17] 2 profile73_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,17,17] 2 profile73_node4_cert).mp (by decide +kernel))

def profile73_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 21 26 25), lower := (rows 1 3 21 26 16), losses := [] }

theorem profile73_node5 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,17,18] 2 :=
  bound_sound (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,17,18] 2 profile73_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,17,18] 2 profile73_node5_cert).mp (by decide +kernel))

def profile73_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node3 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,17] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,17] 2 (by decide) (choices 2) [17,18] profile73_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,17] (choices 2) [17,18] profile73_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile73_node4
  · exact profile73_node5

def profile73_node7_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 3 22 25 25), lower := (rows 1 3 22 25 16), losses := [] }

theorem profile73_node7 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,18,17] 2 :=
  bound_sound (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,18,17] 2 profile73_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,18,17] 2 profile73_node7_cert).mp (by decide +kernel))

def profile73_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node6 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,18] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,18] 2 (by decide) (choices 2) [17] profile73_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,18] (choices 2) [17] profile73_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile73_node7

def profile73_node9_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 3 28 25 19), lower := (rows 1 3 28 25 16), losses := [] }

theorem profile73_node9 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,24,17] 2 :=
  bound_sound (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,24,17] 2 profile73_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,24,17] 2 profile73_node9_cert).mp (by decide +kernel))

def profile73_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node8 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,24] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,24] 2 (by decide) (choices 2) [17] profile73_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1,24] (choices 2) [17] profile73_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile73_node9

def profile73_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node2 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1] 2 (by decide) (choices 2) [17,18,24] profile73_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,1] (choices 2) [17,18,24] profile73_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile73_node3
  · exact profile73_node6
  · exact profile73_node8

def profile73_node12_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 10 21 25 19), lower := (rows 1 10 21 25 16), losses := [] }

theorem profile73_node12 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,8,17,17] 2 :=
  bound_sound (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,8,17,17] 2 profile73_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,8,17,17] 2 profile73_node12_cert).mp (by decide +kernel))

def profile73_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node11 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,8,17] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,8,17] 2 (by decide) (choices 2) [17] profile73_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,8,17] (choices 2) [17] profile73_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile73_node12

def profile73_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node10 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,8] 2 (by decide) (choices 2) [17] profile73_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,8] (choices 2) [17] profile73_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile73_node11

def profile73_node15_cert : Bound 5 := { allowed := (rows 0 0 16 0 1), upper := (rows 1 18 7 25 25), lower := (rows 1 18 7 25 16), losses := [] }

theorem profile73_node15 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,3,17] 2 :=
  bound_sound (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,3,17] 2 profile73_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,3,17] 2 profile73_node15_cert).mp (by decide +kernel))

def profile73_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node14 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,3] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,3] 2 (by decide) (choices 2) [17] profile73_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,3] (choices 2) [17] profile73_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile73_node15

def profile73_node17_cert : Bound 5 := { allowed := (rows 0 0 16 0 1), upper := (rows 1 18 13 25 19), lower := (rows 1 18 13 25 16), losses := [] }

theorem profile73_node17 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,9,17] 2 :=
  bound_sound (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,9,17] 2 profile73_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,9,17] 2 profile73_node17_cert).mp (by decide +kernel))

def profile73_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node16 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,9] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,9] 2 (by decide) (choices 2) [17] profile73_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,9] (choices 2) [17] profile73_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile73_node17

def profile73_node18_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 18 21 11 27), lower := (rows 1 18 21 8 16), losses := [{ target := 4, region := (rows 31 2 4 10 0), good := (rows 1 11 5 9 1) }] }

theorem profile73_node18 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,17] 2 :=
  bound_sound (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,17] 2 profile73_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16,17] 2 profile73_node18_cert).mp (by decide +kernel))

def profile73_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node13 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16] 2 (by decide) (choices 2) [3,9,17] profile73_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0,16] (choices 2) [3,9,17] profile73_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile73_node14
  · exact profile73_node16
  · exact profile73_node18

def profile73_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node1 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0] 2 (by decide) (choices 1) [1,8,16] profile73_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [0] (choices 1) [1,8,16] profile73_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile73_node2
  · exact profile73_node10
  · exact profile73_node13

def profile73_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node0 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [] 2 := by
  apply routed_branch (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [] 2 (by decide) (choices 0) [0] profile73_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [] (choices 0) [0] profile73_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile73_node1

theorem profile73 : Upper (D (n:=5) [3,9,16,17,18]) (R (n:=5) [3,9,16,17,18]) [] 2 := profile73_node0

def profile74_node3_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 7 29 29), lower := (rows 1 3 7 8 16), losses := [] }

theorem profile74_node3 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,3] 2 :=
  bound_sound (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,3] 2 profile74_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,3] 2 profile74_node3_cert).mp (by decide +kernel))

def profile74_node4_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 13 31 23), lower := (rows 1 3 13 8 16), losses := [] }

theorem profile74_node4 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,9] 2 :=
  bound_sound (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,9] 2 profile74_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,9] 2 profile74_node4_cert).mp (by decide +kernel))

def profile74_node6_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 3 14 25 21), lower := (rows 1 3 14 25 16), losses := [] }

theorem profile74_node6 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,10,17] 2 :=
  bound_sound (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,10,17] 2 profile74_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,10,17] 2 profile74_node6_cert).mp (by decide +kernel))

def profile74_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node5 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,10] 2 := by
  apply routed_branch (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,10] 2 (by decide) (choices 2) [17] profile74_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,10] (choices 2) [17] profile74_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile74_node6

def profile74_node8_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 3 28 11 21), lower := (rows 1 3 28 11 16), losses := [] }

theorem profile74_node8 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,24,3] 2 :=
  bound_sound (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,24,3] 2 profile74_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,24,3] 2 profile74_node8_cert).mp (by decide +kernel))

def profile74_node9_cert : Bound 5 := { allowed := (rows 0 0 1 0 1), upper := (rows 1 3 28 13 19), lower := (rows 1 3 28 13 16), losses := [] }

theorem profile74_node9 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,24,5] 2 :=
  bound_sound (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,24,5] 2 profile74_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,24,5] 2 profile74_node9_cert).mp (by decide +kernel))

def profile74_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node7 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,24] 2 := by
  apply routed_branch (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,24] 2 (by decide) (choices 2) [3,5] profile74_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1,24] (choices 2) [3,5] profile74_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile74_node8
  · exact profile74_node9

def profile74_node2_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile74_node2 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1] 2 (by decide) (choices 2) [3,9,10,24] profile74_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,1] (choices 2) [3,9,10,24] profile74_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile74_node3
  · exact profile74_node4
  · exact profile74_node5
  · exact profile74_node7

def profile74_node11_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 6 7 25 25), lower := (rows 1 6 7 8 16), losses := [] }

theorem profile74_node11 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,4,3] 2 :=
  bound_sound (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,4,3] 2 profile74_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,4,3] 2 profile74_node11_cert).mp (by decide +kernel))

def profile74_node12_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 6 13 27 19), lower := (rows 1 6 13 8 16), losses := [] }

theorem profile74_node12 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,4,9] 2 :=
  bound_sound (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,4,9] 2 profile74_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,4,9] 2 profile74_node12_cert).mp (by decide +kernel))

def profile74_node10_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile74_node10 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,4] 2 (by decide) (choices 2) [3,9] profile74_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0,4] (choices 2) [3,9] profile74_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile74_node11
  · exact profile74_node12

def profile74_node1_route : Route 5 := (fun mask => match mask with | 8 => (4,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 16 => (4,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile74_node1 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0] 2 (by decide) (choices 1) [1,4] profile74_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [0] (choices 1) [1,4] profile74_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile74_node2
  · exact profile74_node10

def profile74_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node0 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [] 2 := by
  apply routed_branch (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [] 2 (by decide) (choices 0) [0] profile74_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [] (choices 0) [0] profile74_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile74_node1

theorem profile74 : Upper (D (n:=5) [3,9,17,17,17]) (R (n:=5) [3,9,17,17,17]) [] 2 := profile74_node0

def profile75_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 3 5 14 23), lower := (rows 1 3 5 14 23), losses := [] }

theorem profile75_node5 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,1,6,7] 2 :=
  bound_sound (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,1,6,7] 2 profile75_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,1,6,7] 2 profile75_node5_cert).mp (by decide +kernel))

def profile75_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node4 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,1,6] 2 := by
  apply routed_branch (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,1,6] 2 (by decide) (choices 3) [7] profile75_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,1,6] (choices 3) [7] profile75_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node5

def profile75_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node3 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,1] 2 := by
  apply routed_branch (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,1] 2 (by decide) (choices 2) [6] profile75_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,1] (choices 2) [6] profile75_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node4

def profile75_node8_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 1 3 6 13 23), lower := (rows 1 3 6 13 23), losses := [] }

theorem profile75_node8 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,2,5,7] 2 :=
  bound_sound (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,2,5,7] 2 profile75_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,2,5,7] 2 profile75_node8_cert).mp (by decide +kernel))

def profile75_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node7 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,2,5] 2 := by
  apply routed_branch (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,2,5] 2 (by decide) (choices 3) [7] profile75_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,2,5] (choices 3) [7] profile75_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node8

def profile75_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node6 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,2] 2 := by
  apply routed_branch (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,2] 2 (by decide) (choices 2) [5] profile75_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1,2] (choices 2) [5] profile75_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node7

def profile75_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node2 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1] 2 (by decide) (choices 1) [1,2] profile75_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,1] (choices 1) [1,2] profile75_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile75_node3
  · exact profile75_node6

def profile75_node12_cert : Bound 5 := { allowed := (rows 0 0 0 4 0), upper := (rows 1 6 5 11 23), lower := (rows 1 6 5 11 23), losses := [] }

theorem profile75_node12 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4,1,3,7] 2 :=
  bound_sound (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4,1,3,7] 2 profile75_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4,1,3,7] 2 profile75_node12_cert).mp (by decide +kernel))

def profile75_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node11 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4,1,3] 2 := by
  apply routed_branch (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4,1,3] 2 (by decide) (choices 3) [7] profile75_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4,1,3] (choices 3) [7] profile75_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node12

def profile75_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node10 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4,1] 2 := by
  apply routed_branch (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4,1] 2 (by decide) (choices 2) [3] profile75_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4,1] (choices 2) [3] profile75_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node11

def profile75_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node9 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4] 2 := by
  apply routed_branch (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4] 2 (by decide) (choices 1) [1] profile75_node9_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0,4] (choices 1) [1] profile75_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node10

def profile75_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node1 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0] 2 (by decide) (choices 1) [1,4] profile75_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [0] (choices 1) [1,4] profile75_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile75_node2
  · exact profile75_node9

def profile75_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node0 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [] 2 := by
  apply routed_branch (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [] 2 (by decide) (choices 0) [0] profile75_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [] (choices 0) [0] profile75_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node1

theorem profile75 : Upper (D (n:=5) [3,10,10,16,24]) (R (n:=5) [3,10,10,16,24]) [] 2 := profile75_node0

def profile76_node5_cert : Bound 5 := { allowed := (rows 0 0 2 1 0), upper := (rows 1 3 21 26 19), lower := (rows 1 3 21 26 19), losses := [] }

theorem profile76_node5 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,17,18,3] 2 :=
  bound_sound (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,17,18,3] 2 profile76_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,17,18,3] 2 profile76_node5_cert).mp (by decide +kernel))

def profile76_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node4 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,17,18] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,17,18] 2 (by decide) (choices 2) [3] profile76_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,17,18] (choices 2) [3] profile76_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node5

def profile76_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node3 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,17] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,17] 2 (by decide) (choices 2) [18] profile76_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,17] (choices 2) [18] profile76_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node4

def profile76_node8_cert : Bound 5 := { allowed := (rows 0 0 1 2 0), upper := (rows 1 3 22 25 19), lower := (rows 1 3 22 25 19), losses := [] }

theorem profile76_node8 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,18,17,3] 2 :=
  bound_sound (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,18,17,3] 2 profile76_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,18,17,3] 2 profile76_node8_cert).mp (by decide +kernel))

def profile76_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node7 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,18,17] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,18,17] 2 (by decide) (choices 2) [3] profile76_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,18,17] (choices 2) [3] profile76_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node8

def profile76_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node6 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,18] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,18] 2 (by decide) (choices 2) [17] profile76_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1,18] (choices 2) [17] profile76_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node7

def profile76_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node2 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1] 2 (by decide) (choices 2) [17,18] profile76_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,1] (choices 2) [17,18] profile76_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile76_node3
  · exact profile76_node6

def profile76_node11_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 18 7 25 19), lower := (rows 1 18 7 25 16), losses := [{ target := 1, region := (rows 31 0 4 26 16), good := (rows 1 25 13 25 25) },{ target := 4, region := (rows 31 2 6 8 0), good := (rows 1 7 7 9 1) }] }

theorem profile76_node11 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,3,17] 2 :=
  bound_sound (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,3,17] 2 profile76_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,3,17] 2 profile76_node11_cert).mp (by decide +kernel))

def profile76_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node10 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,3] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,3] 2 (by decide) (choices 2) [17] profile76_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,3] (choices 2) [17] profile76_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node11

def profile76_node13_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 18 21 11 19), lower := (rows 1 18 21 11 16), losses := [{ target := 1, region := (rows 31 0 22 8 16), good := (rows 1 21 21 13 21) },{ target := 4, region := (rows 31 2 4 10 0), good := (rows 1 11 5 11 1) }] }

theorem profile76_node13 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,17,3] 2 :=
  bound_sound (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,17,3] 2 profile76_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,17,3] 2 profile76_node13_cert).mp (by decide +kernel))

def profile76_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node12 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,17] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,17] 2 (by decide) (choices 2) [3] profile76_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16,17] (choices 2) [3] profile76_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node13

def profile76_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node9 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16] 2 (by decide) (choices 2) [3,17] profile76_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0,16] (choices 2) [3,17] profile76_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile76_node10
  · exact profile76_node12

def profile76_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node1 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0] 2 (by decide) (choices 1) [1,16] profile76_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [0] (choices 1) [1,16] profile76_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile76_node2
  · exact profile76_node9

def profile76_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node0 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [] 2 (by decide) (choices 0) [0] profile76_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [] (choices 0) [0] profile76_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node1

theorem profile76 : Upper (D (n:=5) [3,10,16,16,18]) (R (n:=5) [3,10,16,16,18]) [] 2 := profile76_node0

def profile77_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 3 7 25 26), lower := (rows 1 3 7 25 16), losses := [{ target := 1, region := (rows 31 0 4 24 16), good := (rows 1 1 5 25 25) }] }

theorem profile77_node4 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,3,17] 2 :=
  bound_sound (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,3,17] 2 profile77_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,3,17] 2 profile77_node4_cert).mp (by decide +kernel))

def profile77_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 7 26 25), lower := (rows 1 3 7 26 16), losses := [{ target := 1, region := (rows 31 0 4 8 24), good := (rows 1 1 5 25 17) }] }

theorem profile77_node5 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,3,18] 2 :=
  bound_sound (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,3,18] 2 profile77_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,3,18] 2 profile77_node5_cert).mp (by decide +kernel))

def profile77_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node3 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,3] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,3] 2 (by decide) (choices 2) [17,18] profile77_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,3] (choices 2) [17,18] profile77_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node4
  · exact profile77_node5

def profile77_node8_cert : Bound 5 := { allowed := (rows 0 0 2 1 0), upper := (rows 1 3 13 26 19), lower := (rows 1 3 13 26 19), losses := [] }

theorem profile77_node8 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,9,18,3] 2 :=
  bound_sound (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,9,18,3] 2 profile77_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,9,18,3] 2 profile77_node8_cert).mp (by decide +kernel))

def profile77_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node7 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,9,18] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,9,18] 2 (by decide) (choices 2) [3] profile77_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,9,18] (choices 2) [3] profile77_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node8

def profile77_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node6 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,9] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,9] 2 (by decide) (choices 2) [18] profile77_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,9] (choices 2) [18] profile77_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node7

def profile77_node11_cert : Bound 5 := { allowed := (rows 0 0 1 2 0), upper := (rows 1 3 14 25 19), lower := (rows 1 3 14 25 19), losses := [] }

theorem profile77_node11 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,10,17,3] 2 :=
  bound_sound (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,10,17,3] 2 profile77_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,10,17,3] 2 profile77_node11_cert).mp (by decide +kernel))

def profile77_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node10 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,10,17] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,10,17] 2 (by decide) (choices 2) [3] profile77_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,10,17] (choices 2) [3] profile77_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node11

def profile77_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node9 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,10] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,10] 2 (by decide) (choices 2) [17] profile77_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,10] (choices 2) [17] profile77_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node10

def profile77_node14_cert : Bound 5 := { allowed := (rows 0 0 3 0 0), upper := (rows 1 3 28 11 19), lower := (rows 1 3 28 11 19), losses := [] }

theorem profile77_node14 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,24,3,3] 2 :=
  bound_sound (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,24,3,3] 2 profile77_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,24,3,3] 2 profile77_node14_cert).mp (by decide +kernel))

def profile77_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node13 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,24,3] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,24,3] 2 (by decide) (choices 2) [3] profile77_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,24,3] (choices 2) [3] profile77_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node14

def profile77_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node12 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,24] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,24] 2 (by decide) (choices 2) [3] profile77_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1,24] (choices 2) [3] profile77_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node13

def profile77_node2_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile77_node2 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1] 2 (by decide) (choices 2) [3,9,10,24] profile77_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,1] (choices 2) [3,9,10,24] profile77_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile77_node3
  · exact profile77_node6
  · exact profile77_node9
  · exact profile77_node12

def profile77_node17_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 10 7 25 19), lower := (rows 1 10 7 25 16), losses := [{ target := 1, region := (rows 31 0 4 24 16), good := (rows 1 9 5 25 25) }] }

theorem profile77_node17 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,3,17] 2 :=
  bound_sound (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,3,17] 2 profile77_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,3,17] 2 profile77_node17_cert).mp (by decide +kernel))

def profile77_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node16 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,3] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,3] 2 (by decide) (choices 2) [17] profile77_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,3] (choices 2) [17] profile77_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node17

def profile77_node19_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 10 21 11 19), lower := (rows 1 10 21 11 16), losses := [{ target := 1, region := (rows 31 0 20 8 16), good := (rows 1 9 21 9 21) }] }

theorem profile77_node19 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,17,3] 2 :=
  bound_sound (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,17,3] 2 profile77_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,17,3] 2 profile77_node19_cert).mp (by decide +kernel))

def profile77_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node18 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,17] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,17] 2 (by decide) (choices 2) [3] profile77_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8,17] (choices 2) [3] profile77_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node19

def profile77_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node15 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8] 2 (by decide) (choices 2) [3,17] profile77_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0,8] (choices 2) [3,17] profile77_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node16
  · exact profile77_node18

def profile77_node1_route : Route 5 := (fun mask => match mask with | 16 => (8,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile77_node1 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0] 2 (by decide) (choices 1) [1,8] profile77_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [0] (choices 1) [1,8] profile77_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node2
  · exact profile77_node15

def profile77_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node0 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [] 2 := by
  apply routed_branch (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [] 2 (by decide) (choices 0) [0] profile77_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [] (choices 0) [0] profile77_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node1

theorem profile77 : Upper (D (n:=5) [3,10,16,17,17]) (R (n:=5) [3,10,16,17,17]) [] 2 := profile77_node0

def profile78_node5_cert : Bound 5 := { allowed := (rows 0 0 0 1 0), upper := (rows 1 3 7 26 19), lower := (rows 1 3 7 26 19), losses := [] }

theorem profile78_node5 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,3,18,3] 2 :=
  bound_sound (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,3,18,3] 2 profile78_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,3,18,3] 2 profile78_node5_cert).mp (by decide +kernel))

def profile78_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node4 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,3,18] 2 := by
  apply routed_branch (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,3,18] 2 (by decide) (choices 2) [3] profile78_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,3,18] (choices 2) [3] profile78_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node5

def profile78_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node3 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,3] 2 := by
  apply routed_branch (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,3] 2 (by decide) (choices 2) [18] profile78_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,3] (choices 2) [18] profile78_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node4

def profile78_node8_cert : Bound 5 := { allowed := (rows 0 0 1 0 0), upper := (rows 1 3 22 11 19), lower := (rows 1 3 22 11 19), losses := [] }

theorem profile78_node8 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,18,3,3] 2 :=
  bound_sound (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,18,3,3] 2 profile78_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,18,3,3] 2 profile78_node8_cert).mp (by decide +kernel))

def profile78_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node7 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,18,3] 2 := by
  apply routed_branch (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,18,3] 2 (by decide) (choices 2) [3] profile78_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,18,3] (choices 2) [3] profile78_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node8

def profile78_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node6 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,18] 2 := by
  apply routed_branch (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,18] 2 (by decide) (choices 2) [3] profile78_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1,18] (choices 2) [3] profile78_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node7

def profile78_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node2 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1] 2 (by decide) (choices 2) [3,18] profile78_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,1] (choices 2) [3,18] profile78_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile78_node3
  · exact profile78_node6

def profile78_node11_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 18 7 11 19), lower := (rows 1 18 7 11 16), losses := [] }

theorem profile78_node11 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,16,3,3] 2 :=
  bound_sound (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,16,3,3] 2 profile78_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,16,3,3] 2 profile78_node11_cert).mp (by decide +kernel))

def profile78_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node10 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,16,3] 2 := by
  apply routed_branch (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,16,3] 2 (by decide) (choices 2) [3] profile78_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,16,3] (choices 2) [3] profile78_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node11

def profile78_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node9 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,16] 2 := by
  apply routed_branch (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,16] 2 (by decide) (choices 2) [3] profile78_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0,16] (choices 2) [3] profile78_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node10

def profile78_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node1 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0] 2 := by
  apply routed_branch (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0] 2 (by decide) (choices 1) [1,16] profile78_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [0] (choices 1) [1,16] profile78_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile78_node2
  · exact profile78_node9

def profile78_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node0 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [] 2 := by
  apply routed_branch (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [] 2 (by decide) (choices 0) [0] profile78_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [] (choices 0) [0] profile78_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node1

theorem profile78 : Upper (D (n:=5) [3,11,16,16,17]) (R (n:=5) [3,11,16,16,17]) [] 2 := profile78_node0

def profile79_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node0 : Upper (D (n:=5) [3,12,16,16,16]) (R (n:=5) [3,12,16,16,16]) [] 2 := by
  apply routed_branch (D (n:=5) [3,12,16,16,16]) (R (n:=5) [3,12,16,16,16]) [] 2 (by decide) (choices 0) [] profile79_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [3,12,16,16,16]) (R (n:=5) [3,12,16,16,16]) [] (choices 0) [] profile79_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile79 : Upper (D (n:=5) [3,12,16,16,16]) (R (n:=5) [3,12,16,16,16]) [] 2 := profile79_node0

def profile80_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 15 15 15 15 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile80_node0 : Upper (D (n:=5) [4,9,9,9,32]) (R (n:=5) [4,9,9,9,32]) [] 2 :=
  bound_sound (D (n:=5) [4,9,9,9,32]) (R (n:=5) [4,9,9,9,32]) [] 2 profile80_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [4,9,9,9,32]) (R (n:=5) [4,9,9,9,32]) [] 2 profile80_node0_cert).mp (by decide +kernel))

theorem profile80 : Upper (D (n:=5) [4,9,9,9,32]) (R (n:=5) [4,9,9,9,32]) [] 2 := profile80_node0

def profile81_node0_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 23 23 23 31 23), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile81_node0 : Upper (D (n:=5) [4,9,9,16,25]) (R (n:=5) [4,9,9,16,25]) [] 2 :=
  bound_sound (D (n:=5) [4,9,9,16,25]) (R (n:=5) [4,9,9,16,25]) [] 2 profile81_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [4,9,9,16,25]) (R (n:=5) [4,9,9,16,25]) [] 2 profile81_node0_cert).mp (by decide +kernel))

theorem profile81 : Upper (D (n:=5) [4,9,9,16,25]) (R (n:=5) [4,9,9,16,25]) [] 2 := profile81_node0

def profile82_node0_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 15 15 15 15 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile82_node0 : Upper (D (n:=5) [4,9,9,17,24]) (R (n:=5) [4,9,9,17,24]) [] 2 :=
  bound_sound (D (n:=5) [4,9,9,17,24]) (R (n:=5) [4,9,9,17,24]) [] 2 profile82_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [4,9,9,17,24]) (R (n:=5) [4,9,9,17,24]) [] 2 profile82_node0_cert).mp (by decide +kernel))

theorem profile82 : Upper (D (n:=5) [4,9,9,17,24]) (R (n:=5) [4,9,9,17,24]) [] 2 := profile82_node0

def profile83_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 1 3 5 13 23), lower := (rows 1 3 5 13 16), losses := [] }

theorem profile83_node4 : Upper (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0,1,1,5] 2 :=
  bound_sound (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0,1,1,5] 2 profile83_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0,1,1,5] 2 profile83_node4_cert).mp (by decide +kernel))

def profile83_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile83_node3 : Upper (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0,1,1] 2 := by
  apply routed_branch (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0,1,1] 2 (by decide) (choices 2) [5] profile83_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0,1,1] (choices 2) [5] profile83_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile83_node4

def profile83_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile83_node2 : Upper (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0,1] 2 (by decide) (choices 1) [1] profile83_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0,1] (choices 1) [1] profile83_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile83_node3

def profile83_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile83_node1 : Upper (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0] 2 := by
  apply routed_branch (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0] 2 (by decide) (choices 1) [1] profile83_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [0] (choices 1) [1] profile83_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile83_node2

def profile83_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile83_node0 : Upper (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [] 2 := by
  apply routed_branch (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [] 2 (by decide) (choices 0) [0] profile83_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [] (choices 0) [0] profile83_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile83_node1

theorem profile83 : Upper (D (n:=5) [4,9,10,16,24]) (R (n:=5) [4,9,10,16,24]) [] 2 := profile83_node0

def profile84_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 1), upper := (rows 1 3 21 25 19), lower := (rows 1 3 21 25 16), losses := [] }

theorem profile84_node4 : Upper (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0,1,17,17] 2 :=
  bound_sound (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0,1,17,17] 2 profile84_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0,1,17,17] 2 profile84_node4_cert).mp (by decide +kernel))

def profile84_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node3 : Upper (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0,1,17] 2 := by
  apply routed_branch (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0,1,17] 2 (by decide) (choices 2) [17] profile84_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0,1,17] (choices 2) [17] profile84_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile84_node4

def profile84_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node2 : Upper (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0,1] 2 (by decide) (choices 2) [17] profile84_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0,1] (choices 2) [17] profile84_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile84_node3

def profile84_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node1 : Upper (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0] 2 := by
  apply routed_branch (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0] 2 (by decide) (choices 1) [1] profile84_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [0] (choices 1) [1] profile84_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile84_node2

def profile84_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node0 : Upper (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [] 2 := by
  apply routed_branch (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [] 2 (by decide) (choices 0) [0] profile84_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [] (choices 0) [0] profile84_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile84_node1

theorem profile84 : Upper (D (n:=5) [4,9,16,16,18]) (R (n:=5) [4,9,16,16,18]) [] 2 := profile84_node0

def profile85_node3_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 7 25 25), lower := (rows 1 3 7 8 16), losses := [] }

theorem profile85_node3 : Upper (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0,1,3] 2 :=
  bound_sound (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0,1,3] 2 profile85_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0,1,3] 2 profile85_node3_cert).mp (by decide +kernel))

def profile85_node4_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 1 3 13 27 19), lower := (rows 1 3 13 8 16), losses := [] }

theorem profile85_node4 : Upper (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0,1,9] 2 :=
  bound_sound (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0,1,9] 2 profile85_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0,1,9] 2 profile85_node4_cert).mp (by decide +kernel))

def profile85_node2_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile85_node2 : Upper (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0,1] 2 (by decide) (choices 2) [3,9] profile85_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0,1] (choices 2) [3,9] profile85_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile85_node3
  · exact profile85_node4

def profile85_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node1 : Upper (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0] 2 := by
  apply routed_branch (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0] 2 (by decide) (choices 1) [1] profile85_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [0] (choices 1) [1] profile85_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile85_node2

def profile85_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node0 : Upper (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [] 2 := by
  apply routed_branch (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [] 2 (by decide) (choices 0) [0] profile85_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [] (choices 0) [0] profile85_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile85_node1

theorem profile85 : Upper (D (n:=5) [4,9,16,17,17]) (R (n:=5) [4,9,16,17,17]) [] 2 := profile85_node0

def profile86_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 3 7 25 19), lower := (rows 1 3 7 25 16), losses := [{ target := 1, region := (rows 31 0 4 24 16), good := (rows 1 1 5 25 25) }] }

theorem profile86_node4 : Upper (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,3,17] 2 :=
  bound_sound (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,3,17] 2 profile86_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,3,17] 2 profile86_node4_cert).mp (by decide +kernel))

def profile86_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node3 : Upper (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,3] 2 := by
  apply routed_branch (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,3] 2 (by decide) (choices 2) [17] profile86_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,3] (choices 2) [17] profile86_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile86_node4

def profile86_node6_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 3 21 11 19), lower := (rows 1 3 21 11 16), losses := [{ target := 1, region := (rows 31 0 20 8 16), good := (rows 1 1 21 9 21) }] }

theorem profile86_node6 : Upper (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,17,3] 2 :=
  bound_sound (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,17,3] 2 profile86_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,17,3] 2 profile86_node6_cert).mp (by decide +kernel))

def profile86_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node5 : Upper (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,17] 2 := by
  apply routed_branch (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,17] 2 (by decide) (choices 2) [3] profile86_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1,17] (choices 2) [3] profile86_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile86_node6

def profile86_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node2 : Upper (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1] 2 (by decide) (choices 2) [3,17] profile86_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0,1] (choices 2) [3,17] profile86_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile86_node3
  · exact profile86_node5

def profile86_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node1 : Upper (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0] 2 := by
  apply routed_branch (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0] 2 (by decide) (choices 1) [1] profile86_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [0] (choices 1) [1] profile86_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile86_node2

def profile86_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node0 : Upper (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [] 2 := by
  apply routed_branch (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [] 2 (by decide) (choices 0) [0] profile86_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [] (choices 0) [0] profile86_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile86_node1

theorem profile86 : Upper (D (n:=5) [4,10,16,16,17]) (R (n:=5) [4,10,16,16,17]) [] 2 := profile86_node0

def profile87_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 1 3 7 11 19), lower := (rows 1 3 7 11 16), losses := [] }

theorem profile87_node4 : Upper (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0,1,3,3] 2 :=
  bound_sound (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0,1,3,3] 2 profile87_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0,1,3,3] 2 profile87_node4_cert).mp (by decide +kernel))

def profile87_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node3 : Upper (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0,1,3] 2 := by
  apply routed_branch (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0,1,3] 2 (by decide) (choices 2) [3] profile87_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0,1,3] (choices 2) [3] profile87_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile87_node4

def profile87_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node2 : Upper (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0,1] 2 := by
  apply routed_branch (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0,1] 2 (by decide) (choices 2) [3] profile87_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0,1] (choices 2) [3] profile87_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile87_node3

def profile87_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node1 : Upper (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0] 2 := by
  apply routed_branch (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0] 2 (by decide) (choices 1) [1] profile87_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [0] (choices 1) [1] profile87_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile87_node2

def profile87_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node0 : Upper (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [] 2 := by
  apply routed_branch (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [] 2 (by decide) (choices 0) [0] profile87_node0_route
    (by change RowCover 5 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [] (choices 0) [0] profile87_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile87_node1

theorem profile87 : Upper (D (n:=5) [4,11,16,16,16]) (R (n:=5) [4,11,16,16,16]) [] 2 := profile87_node0

def profile88_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 0), upper := (rows 31 31 31 31 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile88_node0 : Upper (D (n:=5) [9,9,9,9,27]) (R (n:=5) [9,9,9,9,27]) [] 2 :=
  bound_sound (D (n:=5) [9,9,9,9,27]) (R (n:=5) [9,9,9,9,27]) [] 2 profile88_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,9,9,27]) (R (n:=5) [9,9,9,9,27]) [] 2 profile88_node0_cert).mp (by decide +kernel))

theorem profile88 : Upper (D (n:=5) [9,9,9,9,27]) (R (n:=5) [9,9,9,9,27]) [] 2 := profile88_node0

def profile89_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 8), upper := (rows 31 31 31 31 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile89_node0 : Upper (D (n:=5) [9,9,9,10,26]) (R (n:=5) [9,9,9,10,26]) [] 2 :=
  bound_sound (D (n:=5) [9,9,9,10,26]) (R (n:=5) [9,9,9,10,26]) [] 2 profile89_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,9,10,26]) (R (n:=5) [9,9,9,10,26]) [] 2 profile89_node0_cert).mp (by decide +kernel))

theorem profile89 : Upper (D (n:=5) [9,9,9,10,26]) (R (n:=5) [9,9,9,10,26]) [] 2 := profile89_node0

def profile90_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 8), upper := (rows 31 31 31 31 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile90_node0 : Upper (D (n:=5) [9,9,9,11,25]) (R (n:=5) [9,9,9,11,25]) [] 2 :=
  bound_sound (D (n:=5) [9,9,9,11,25]) (R (n:=5) [9,9,9,11,25]) [] 2 profile90_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,9,11,25]) (R (n:=5) [9,9,9,11,25]) [] 2 profile90_node0_cert).mp (by decide +kernel))

theorem profile90 : Upper (D (n:=5) [9,9,9,11,25]) (R (n:=5) [9,9,9,11,25]) [] 2 := profile90_node0

def profile91_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 8), upper := (rows 15 15 15 15 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile91_node0 : Upper (D (n:=5) [9,9,9,12,24]) (R (n:=5) [9,9,9,12,24]) [] 2 :=
  bound_sound (D (n:=5) [9,9,9,12,24]) (R (n:=5) [9,9,9,12,24]) [] 2 profile91_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,9,12,24]) (R (n:=5) [9,9,9,12,24]) [] 2 profile91_node0_cert).mp (by decide +kernel))

theorem profile91 : Upper (D (n:=5) [9,9,9,12,24]) (R (n:=5) [9,9,9,12,24]) [] 2 := profile91_node0

def profile92_node0_cert : Bound 5 := { allowed := (rows 0 0 0 16 0), upper := (rows 23 23 23 31 23), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile92_node0 : Upper (D (n:=5) [9,9,9,16,20]) (R (n:=5) [9,9,9,16,20]) [] 2 :=
  bound_sound (D (n:=5) [9,9,9,16,20]) (R (n:=5) [9,9,9,16,20]) [] 2 profile92_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,9,16,20]) (R (n:=5) [9,9,9,16,20]) [] 2 profile92_node0_cert).mp (by decide +kernel))

theorem profile92 : Upper (D (n:=5) [9,9,9,16,20]) (R (n:=5) [9,9,9,16,20]) [] 2 := profile92_node0

def profile93_node0_cert : Bound 5 := { allowed := (rows 0 0 0 16 0), upper := (rows 31 31 31 31 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile93_node0 : Upper (D (n:=5) [9,9,9,17,19]) (R (n:=5) [9,9,9,17,19]) [] 2 :=
  bound_sound (D (n:=5) [9,9,9,17,19]) (R (n:=5) [9,9,9,17,19]) [] 2 profile93_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,9,17,19]) (R (n:=5) [9,9,9,17,19]) [] 2 profile93_node0_cert).mp (by decide +kernel))

theorem profile93 : Upper (D (n:=5) [9,9,9,17,19]) (R (n:=5) [9,9,9,17,19]) [] 2 := profile93_node0

def profile94_node0_cert : Bound 5 := { allowed := (rows 0 0 0 16 8), upper := (rows 31 31 31 31 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile94_node0 : Upper (D (n:=5) [9,9,9,18,18]) (R (n:=5) [9,9,9,18,18]) [] 2 :=
  bound_sound (D (n:=5) [9,9,9,18,18]) (R (n:=5) [9,9,9,18,18]) [] 2 profile94_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,9,18,18]) (R (n:=5) [9,9,9,18,18]) [] 2 profile94_node0_cert).mp (by decide +kernel))

theorem profile94 : Upper (D (n:=5) [9,9,9,18,18]) (R (n:=5) [9,9,9,18,18]) [] 2 := profile94_node0

def profile95_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 12), upper := (rows 31 31 31 31 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile95_node0 : Upper (D (n:=5) [9,9,10,10,25]) (R (n:=5) [9,9,10,10,25]) [] 2 :=
  bound_sound (D (n:=5) [9,9,10,10,25]) (R (n:=5) [9,9,10,10,25]) [] 2 profile95_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,10,25]) (R (n:=5) [9,9,10,10,25]) [] 2 profile95_node0_cert).mp (by decide +kernel))

theorem profile95 : Upper (D (n:=5) [9,9,10,10,25]) (R (n:=5) [9,9,10,10,25]) [] 2 := profile95_node0

def profile96_node0_cert : Bound 5 := { allowed := (rows 0 0 0 0 12), upper := (rows 15 15 15 15 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile96_node0 : Upper (D (n:=5) [9,9,10,11,24]) (R (n:=5) [9,9,10,11,24]) [] 2 :=
  bound_sound (D (n:=5) [9,9,10,11,24]) (R (n:=5) [9,9,10,11,24]) [] 2 profile96_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,11,24]) (R (n:=5) [9,9,10,11,24]) [] 2 profile96_node0_cert).mp (by decide +kernel))

theorem profile96 : Upper (D (n:=5) [9,9,10,11,24]) (R (n:=5) [9,9,10,11,24]) [] 2 := profile96_node0

def profile97_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 3 18 20 28 21), lower := (rows 3 18 20 28 16), losses := [] }

theorem profile97_node4 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2,16,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2,16,16,20] 2 profile97_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2,16,16,20] 2 profile97_node4_cert).mp (by decide +kernel))

def profile97_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node3 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2,16,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2,16,16] 2 (by decide) (choices 2) [20] profile97_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2,16,16] (choices 2) [20] profile97_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node4

def profile97_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node2 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2,16] 2 (by decide) (choices 1) [16] profile97_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2,16] (choices 1) [16] profile97_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node3

def profile97_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node1 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2] 2 (by decide) (choices 1) [16] profile97_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [2] (choices 1) [16] profile97_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node2

def profile97_node8_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 18 20 25 22), lower := (rows 5 18 20 25 16), losses := [] }

theorem profile97_node8 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16,17] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16,17] 2 profile97_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16,17] 2 profile97_node8_cert).mp (by decide +kernel))

def profile97_node9_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 18 20 26 21), lower := (rows 5 18 20 26 16), losses := [] }

theorem profile97_node9 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16,18] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16,18] 2 profile97_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16,18] 2 profile97_node9_cert).mp (by decide +kernel))

def profile97_node10_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 5 18 20 28 19), lower := (rows 5 18 20 28 16), losses := [] }

theorem profile97_node10 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16,20] 2 profile97_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16,20] 2 profile97_node10_cert).mp (by decide +kernel))

def profile97_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node7 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16] 2 (by decide) (choices 2) [17,18,20] profile97_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16,16] (choices 2) [17,18,20] profile97_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile97_node8
  · exact profile97_node9
  · exact profile97_node10

def profile97_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node6 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16] 2 (by decide) (choices 1) [16] profile97_node6_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4,16] (choices 1) [16] profile97_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node7

def profile97_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node5 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4] 2 (by decide) (choices 1) [16] profile97_node5_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [4] (choices 1) [16] profile97_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node6

def profile97_node14_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 3 20 28 22), lower := (rows 17 3 20 28 16), losses := [] }

theorem profile97_node14 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,1,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,1,16,20] 2 profile97_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,1,16,20] 2 profile97_node14_cert).mp (by decide +kernel))

def profile97_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node13 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,1,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,1,16] 2 (by decide) (choices 2) [20] profile97_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,1,16] (choices 2) [20] profile97_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node14

def profile97_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node12 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,1] 2 (by decide) (choices 1) [16] profile97_node12_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,1] (choices 1) [16] profile97_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node13

def profile97_node17_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 17 6 20 25 22), lower := (rows 17 6 20 25 16), losses := [] }

theorem profile97_node17 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16,17] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16,17] 2 profile97_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16,17] 2 profile97_node17_cert).mp (by decide +kernel))

def profile97_node18_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 17 6 20 26 21), lower := (rows 17 6 20 26 16), losses := [] }

theorem profile97_node18 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16,18] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16,18] 2 profile97_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16,18] 2 profile97_node18_cert).mp (by decide +kernel))

def profile97_node19_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 6 20 28 19), lower := (rows 17 6 20 28 16), losses := [] }

theorem profile97_node19 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16,20] 2 profile97_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16,20] 2 profile97_node19_cert).mp (by decide +kernel))

def profile97_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node16 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16] 2 (by decide) (choices 2) [17,18,20] profile97_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4,16] (choices 2) [17,18,20] profile97_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile97_node17
  · exact profile97_node18
  · exact profile97_node19

def profile97_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node15 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4] 2 (by decide) (choices 1) [16] profile97_node15_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,4] (choices 1) [16] profile97_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node16

def profile97_node22_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 18 5 28 22), lower := (rows 17 18 5 28 16), losses := [] }

theorem profile97_node22 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,1,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,1,20] 2 profile97_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,1,20] 2 profile97_node22_cert).mp (by decide +kernel))

def profile97_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node21 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,1] 2 (by decide) (choices 2) [20] profile97_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,1] (choices 2) [20] profile97_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node22

def profile97_node24_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 18 6 28 21), lower := (rows 17 18 6 28 16), losses := [] }

theorem profile97_node24 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,2,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,2,20] 2 profile97_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,2,20] 2 profile97_node24_cert).mp (by decide +kernel))

def profile97_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node23 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,2] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,2] 2 (by decide) (choices 2) [20] profile97_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,2] (choices 2) [20] profile97_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node24

def profile97_node26_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 18 20 13 22), lower := (rows 17 18 20 13 16), losses := [] }

theorem profile97_node26 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,16,5] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,16,5] 2 profile97_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,16,5] 2 profile97_node26_cert).mp (by decide +kernel))

def profile97_node27_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 18 20 14 21), lower := (rows 17 18 20 14 16), losses := [] }

theorem profile97_node27 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,16,6] 2 :=
  bound_sound (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,16,6] 2 profile97_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,16,6] 2 profile97_node27_cert).mp (by decide +kernel))

def profile97_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node25 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,16] 2 (by decide) (choices 2) [5,6] profile97_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16,16] (choices 2) [5,6] profile97_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile97_node26
  · exact profile97_node27

def profile97_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node20 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16] 2 (by decide) (choices 1) [1,2,16] profile97_node20_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16,16] (choices 1) [1,2,16] profile97_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile97_node21
  · exact profile97_node23
  · exact profile97_node25

def profile97_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node11 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16] 2 (by decide) (choices 1) [1,4,16] profile97_node11_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [16] (choices 1) [1,4,16] profile97_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile97_node12
  · exact profile97_node15
  · exact profile97_node20

def profile97_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node0 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [] 2 (by decide) (choices 1) [2,4,16] profile97_node0_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [] (choices 1) [2,4,16] profile97_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile97_node1
  · exact profile97_node5
  · exact profile97_node11

theorem profile97 : Upper (D (n:=5) [9,9,10,16,19]) (R (n:=5) [9,9,10,16,19]) [] 2 := profile97_node0

def profile98_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 3 3 20 28 28), lower := (rows 3 3 20 28 16), losses := [] }

theorem profile98_node4 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,1,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,1,16,20] 2 profile98_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,1,16,20] 2 profile98_node4_cert).mp (by decide +kernel))

def profile98_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node3 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,1,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,1,16] 2 (by decide) (choices 2) [20] profile98_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,1,16] (choices 2) [20] profile98_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node4

def profile98_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node2 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,1] 2 (by decide) (choices 1) [16] profile98_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,1] (choices 1) [16] profile98_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node3

def profile98_node7_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 3 6 20 25 28), lower := (rows 3 6 20 25 16), losses := [] }

theorem profile98_node7 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4,16,17] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4,16,17] 2 profile98_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4,16,17] 2 profile98_node7_cert).mp (by decide +kernel))

def profile98_node8_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 3 6 20 28 25), lower := (rows 3 6 20 28 16), losses := [] }

theorem profile98_node8 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4,16,20] 2 profile98_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4,16,20] 2 profile98_node8_cert).mp (by decide +kernel))

def profile98_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node6 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4,16] 2 (by decide) (choices 2) [17,20] profile98_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4,16] (choices 2) [17,20] profile98_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile98_node7
  · exact profile98_node8

def profile98_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node5 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4] 2 (by decide) (choices 1) [16] profile98_node5_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,4] (choices 1) [16] profile98_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node6

def profile98_node11_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 3 10 20 28 21), lower := (rows 3 10 20 28 16), losses := [] }

theorem profile98_node11 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,8,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,8,16,20] 2 profile98_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,8,16,20] 2 profile98_node11_cert).mp (by decide +kernel))

def profile98_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node10 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,8,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,8,16] 2 (by decide) (choices 2) [20] profile98_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,8,16] (choices 2) [20] profile98_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node11

def profile98_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node9 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,8] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,8] 2 (by decide) (choices 1) [16] profile98_node9_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,8] (choices 1) [16] profile98_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node10

def profile98_node14_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 3 18 5 28 28), lower := (rows 3 18 5 28 16), losses := [] }

theorem profile98_node14 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,1,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,1,20] 2 profile98_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,1,20] 2 profile98_node14_cert).mp (by decide +kernel))

def profile98_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node13 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,1] 2 (by decide) (choices 2) [20] profile98_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,1] (choices 2) [20] profile98_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node14

def profile98_node16_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 3 18 12 28 21), lower := (rows 3 18 12 28 16), losses := [] }

theorem profile98_node16 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,8,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,8,20] 2 profile98_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,8,20] 2 profile98_node16_cert).mp (by decide +kernel))

def profile98_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node15 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,8] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,8] 2 (by decide) (choices 2) [20] profile98_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,8] (choices 2) [20] profile98_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node16

def profile98_node18_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 3 18 20 13 28), lower := (rows 3 18 20 13 16), losses := [] }

theorem profile98_node18 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,16,5] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,16,5] 2 profile98_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,16,5] 2 profile98_node18_cert).mp (by decide +kernel))

def profile98_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node17 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,16] 2 (by decide) (choices 2) [5] profile98_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16,16] (choices 2) [5] profile98_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node18

def profile98_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node12 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16] 2 (by decide) (choices 1) [1,8,16] profile98_node12_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2,16] (choices 1) [1,8,16] profile98_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node13
  · exact profile98_node15
  · exact profile98_node17

def profile98_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node1 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2] 2 (by decide) (choices 1) [1,4,8,16] profile98_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [2] (choices 1) [1,4,8,16] profile98_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile98_node2
  · exact profile98_node5
  · exact profile98_node9
  · exact profile98_node12

def profile98_node22_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 3 20 26 28), lower := (rows 5 3 20 26 16), losses := [] }

theorem profile98_node22 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1,16,18] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1,16,18] 2 profile98_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1,16,18] 2 profile98_node22_cert).mp (by decide +kernel))

def profile98_node23_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 5 3 20 28 26), lower := (rows 5 3 20 28 16), losses := [] }

theorem profile98_node23 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1,16,20] 2 profile98_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1,16,20] 2 profile98_node23_cert).mp (by decide +kernel))

def profile98_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node21 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1,16] 2 (by decide) (choices 2) [18,20] profile98_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1,16] (choices 2) [18,20] profile98_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile98_node22
  · exact profile98_node23

def profile98_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node20 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1] 2 (by decide) (choices 1) [16] profile98_node20_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,1] (choices 1) [16] profile98_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node21

def profile98_node26_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 6 20 25 26), lower := (rows 5 6 20 25 16), losses := [] }

theorem profile98_node26 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4,16,17] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4,16,17] 2 profile98_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4,16,17] 2 profile98_node26_cert).mp (by decide +kernel))

def profile98_node27_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 6 20 26 25), lower := (rows 5 6 20 26 16), losses := [] }

theorem profile98_node27 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4,16,18] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4,16,18] 2 profile98_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4,16,18] 2 profile98_node27_cert).mp (by decide +kernel))

def profile98_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node25 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4,16] 2 (by decide) (choices 2) [17,18] profile98_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4,16] (choices 2) [17,18] profile98_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile98_node26
  · exact profile98_node27

def profile98_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node24 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4] 2 (by decide) (choices 1) [16] profile98_node24_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,4] (choices 1) [16] profile98_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node25

def profile98_node30_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 10 20 25 22), lower := (rows 5 10 20 25 16), losses := [] }

theorem profile98_node30 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16,17] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16,17] 2 profile98_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16,17] 2 profile98_node30_cert).mp (by decide +kernel))

def profile98_node31_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 10 20 26 21), lower := (rows 5 10 20 26 16), losses := [] }

theorem profile98_node31 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16,18] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16,18] 2 profile98_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16,18] 2 profile98_node31_cert).mp (by decide +kernel))

def profile98_node32_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 5 10 20 28 19), lower := (rows 5 10 20 28 16), losses := [] }

theorem profile98_node32 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16,20] 2 profile98_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16,20] 2 profile98_node32_cert).mp (by decide +kernel))

def profile98_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node29 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16] 2 (by decide) (choices 2) [17,18,20] profile98_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8,16] (choices 2) [17,18,20] profile98_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node30
  · exact profile98_node31
  · exact profile98_node32

def profile98_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node28 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8] 2 (by decide) (choices 1) [16] profile98_node28_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,8] (choices 1) [16] profile98_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node29

def profile98_node35_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 18 5 26 28), lower := (rows 5 18 5 26 16), losses := [] }

theorem profile98_node35 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,1,18] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,1,18] 2 profile98_node35_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,1,18] 2 profile98_node35_cert).mp (by decide +kernel))

def profile98_node36_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 5 18 5 28 26), lower := (rows 5 18 5 28 16), losses := [] }

theorem profile98_node36 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,1,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,1,20] 2 profile98_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,1,20] 2 profile98_node36_cert).mp (by decide +kernel))

def profile98_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node34 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,1] 2 (by decide) (choices 2) [18,20] profile98_node34_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,1] (choices 2) [18,20] profile98_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile98_node35
  · exact profile98_node36

def profile98_node38_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 18 6 25 28), lower := (rows 5 18 6 25 16), losses := [] }

theorem profile98_node38 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,2,17] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,2,17] 2 profile98_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,2,17] 2 profile98_node38_cert).mp (by decide +kernel))

def profile98_node39_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 5 18 6 28 25), lower := (rows 5 18 6 28 16), losses := [] }

theorem profile98_node39 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,2,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,2,20] 2 profile98_node39_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,2,20] 2 profile98_node39_cert).mp (by decide +kernel))

def profile98_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node37 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,2] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,2] 2 (by decide) (choices 2) [17,20] profile98_node37_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,2] (choices 2) [17,20] profile98_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile98_node38
  · exact profile98_node39

def profile98_node41_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 18 12 25 22), lower := (rows 5 18 12 25 16), losses := [] }

theorem profile98_node41 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8,17] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8,17] 2 profile98_node41_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8,17] 2 profile98_node41_cert).mp (by decide +kernel))

def profile98_node42_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 18 12 26 21), lower := (rows 5 18 12 26 16), losses := [] }

theorem profile98_node42 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8,18] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8,18] 2 profile98_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8,18] 2 profile98_node42_cert).mp (by decide +kernel))

def profile98_node43_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 5 18 12 28 19), lower := (rows 5 18 12 28 16), losses := [] }

theorem profile98_node43 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8,20] 2 profile98_node43_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8,20] 2 profile98_node43_cert).mp (by decide +kernel))

def profile98_node40_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node40 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8] 2 (by decide) (choices 2) [17,18,20] profile98_node40_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,8] (choices 2) [17,18,20] profile98_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node41
  · exact profile98_node42
  · exact profile98_node43

def profile98_node45_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 5 18 20 11 28), lower := (rows 5 18 20 11 16), losses := [{ target := 2, region := (rows 1 22 0 9 16), good := (rows 11 18 18 11 18) }] }

theorem profile98_node45 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16,3] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16,3] 2 profile98_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16,3] 2 profile98_node45_cert).mp (by decide +kernel))

def profile98_node46_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 5 18 20 13 26), lower := (rows 5 18 20 13 16), losses := [] }

theorem profile98_node46 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16,5] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16,5] 2 profile98_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16,5] 2 profile98_node46_cert).mp (by decide +kernel))

def profile98_node47_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 5 18 20 14 25), lower := (rows 5 18 20 14 16), losses := [] }

theorem profile98_node47 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16,6] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16,6] 2 profile98_node47_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16,6] 2 profile98_node47_cert).mp (by decide +kernel))

def profile98_node44_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node44 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16] 2 (by decide) (choices 2) [3,5,6] profile98_node44_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16,16] (choices 2) [3,5,6] profile98_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node45
  · exact profile98_node46
  · exact profile98_node47

def profile98_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node33 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16] 2 (by decide) (choices 1) [1,2,8,16] profile98_node33_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4,16] (choices 1) [1,2,8,16] profile98_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile98_node34
  · exact profile98_node37
  · exact profile98_node40
  · exact profile98_node44

def profile98_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node19 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4] 2 (by decide) (choices 1) [1,4,8,16] profile98_node19_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [4] (choices 1) [1,4,8,16] profile98_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile98_node20
  · exact profile98_node24
  · exact profile98_node28
  · exact profile98_node33

def profile98_node51_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 9 3 20 28 22), lower := (rows 9 3 20 28 16), losses := [] }

theorem profile98_node51 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,1,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,1,16,20] 2 profile98_node51_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,1,16,20] 2 profile98_node51_cert).mp (by decide +kernel))

def profile98_node50_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node50 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,1,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,1,16] 2 (by decide) (choices 2) [20] profile98_node50_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,1,16] (choices 2) [20] profile98_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node51

def profile98_node49_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node49 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,1] 2 (by decide) (choices 1) [16] profile98_node49_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,1] (choices 1) [16] profile98_node49_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node50

def profile98_node54_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 9 6 20 25 22), lower := (rows 9 6 20 25 16), losses := [] }

theorem profile98_node54 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16,17] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16,17] 2 profile98_node54_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16,17] 2 profile98_node54_cert).mp (by decide +kernel))

def profile98_node55_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 9 6 20 26 21), lower := (rows 9 6 20 26 16), losses := [] }

theorem profile98_node55 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16,18] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16,18] 2 profile98_node55_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16,18] 2 profile98_node55_cert).mp (by decide +kernel))

def profile98_node56_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 9 6 20 28 19), lower := (rows 9 6 20 28 16), losses := [] }

theorem profile98_node56 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16,20] 2 profile98_node56_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16,20] 2 profile98_node56_cert).mp (by decide +kernel))

def profile98_node53_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node53 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16] 2 (by decide) (choices 2) [17,18,20] profile98_node53_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4,16] (choices 2) [17,18,20] profile98_node53_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node54
  · exact profile98_node55
  · exact profile98_node56

def profile98_node52_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node52 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4] 2 (by decide) (choices 1) [16] profile98_node52_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,4] (choices 1) [16] profile98_node52_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node53

def profile98_node59_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 9 18 5 28 22), lower := (rows 9 18 5 28 16), losses := [] }

theorem profile98_node59 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,1,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,1,20] 2 profile98_node59_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,1,20] 2 profile98_node59_cert).mp (by decide +kernel))

def profile98_node58_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node58 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,1] 2 (by decide) (choices 2) [20] profile98_node58_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,1] (choices 2) [20] profile98_node58_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node59

def profile98_node61_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 9 18 6 28 21), lower := (rows 9 18 6 28 16), losses := [] }

theorem profile98_node61 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,2,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,2,20] 2 profile98_node61_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,2,20] 2 profile98_node61_cert).mp (by decide +kernel))

def profile98_node60_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node60 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,2] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,2] 2 (by decide) (choices 2) [20] profile98_node60_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,2] (choices 2) [20] profile98_node60_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node61

def profile98_node63_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 9 18 20 13 22), lower := (rows 9 18 20 13 16), losses := [] }

theorem profile98_node63 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,16,5] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,16,5] 2 profile98_node63_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,16,5] 2 profile98_node63_cert).mp (by decide +kernel))

def profile98_node64_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 9 18 20 14 21), lower := (rows 9 18 20 14 16), losses := [] }

theorem profile98_node64 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,16,6] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,16,6] 2 profile98_node64_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,16,6] 2 profile98_node64_cert).mp (by decide +kernel))

def profile98_node62_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node62 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,16] 2 (by decide) (choices 2) [5,6] profile98_node62_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16,16] (choices 2) [5,6] profile98_node62_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile98_node63
  · exact profile98_node64

def profile98_node57_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node57 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16] 2 (by decide) (choices 1) [1,2,16] profile98_node57_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8,16] (choices 1) [1,2,16] profile98_node57_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node58
  · exact profile98_node60
  · exact profile98_node62

def profile98_node48_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node48 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8] 2 (by decide) (choices 1) [1,4,16] profile98_node48_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [8] (choices 1) [1,4,16] profile98_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node49
  · exact profile98_node52
  · exact profile98_node57

def profile98_node68_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 3 6 28 28), lower := (rows 17 3 6 28 16), losses := [] }

theorem profile98_node68 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,2,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,2,20] 2 profile98_node68_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,2,20] 2 profile98_node68_cert).mp (by decide +kernel))

def profile98_node67_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node67 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,2] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,2] 2 (by decide) (choices 2) [20] profile98_node67_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,2] (choices 2) [20] profile98_node67_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node68

def profile98_node70_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 3 12 28 22), lower := (rows 17 3 12 28 16), losses := [] }

theorem profile98_node70 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,8,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,8,20] 2 profile98_node70_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,8,20] 2 profile98_node70_cert).mp (by decide +kernel))

def profile98_node69_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node69 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,8] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,8] 2 (by decide) (choices 2) [20] profile98_node69_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,8] (choices 2) [20] profile98_node69_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node70

def profile98_node72_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 3 20 14 28), lower := (rows 17 3 20 14 16), losses := [] }

theorem profile98_node72 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,16,6] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,16,6] 2 profile98_node72_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,16,6] 2 profile98_node72_cert).mp (by decide +kernel))

def profile98_node71_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node71 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,16] 2 (by decide) (choices 2) [6] profile98_node71_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1,16] (choices 2) [6] profile98_node71_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node72

def profile98_node66_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node66 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1] 2 (by decide) (choices 1) [2,8,16] profile98_node66_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,1] (choices 1) [2,8,16] profile98_node66_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node67
  · exact profile98_node69
  · exact profile98_node71

def profile98_node75_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 17 6 5 26 28), lower := (rows 17 6 5 26 16), losses := [] }

theorem profile98_node75 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,1,18] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,1,18] 2 profile98_node75_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,1,18] 2 profile98_node75_cert).mp (by decide +kernel))

def profile98_node76_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 6 5 28 26), lower := (rows 17 6 5 28 16), losses := [] }

theorem profile98_node76 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,1,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,1,20] 2 profile98_node76_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,1,20] 2 profile98_node76_cert).mp (by decide +kernel))

def profile98_node74_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node74 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,1] 2 (by decide) (choices 2) [18,20] profile98_node74_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,1] (choices 2) [18,20] profile98_node74_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile98_node75
  · exact profile98_node76

def profile98_node78_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 17 6 6 25 28), lower := (rows 17 6 6 25 16), losses := [] }

theorem profile98_node78 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,2,17] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,2,17] 2 profile98_node78_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,2,17] 2 profile98_node78_cert).mp (by decide +kernel))

def profile98_node79_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 6 6 28 25), lower := (rows 17 6 6 28 16), losses := [] }

theorem profile98_node79 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,2,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,2,20] 2 profile98_node79_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,2,20] 2 profile98_node79_cert).mp (by decide +kernel))

def profile98_node77_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node77 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,2] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,2] 2 (by decide) (choices 2) [17,20] profile98_node77_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,2] (choices 2) [17,20] profile98_node77_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile98_node78
  · exact profile98_node79

def profile98_node81_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 17 6 12 25 22), lower := (rows 17 6 12 25 16), losses := [] }

theorem profile98_node81 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8,17] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8,17] 2 profile98_node81_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8,17] 2 profile98_node81_cert).mp (by decide +kernel))

def profile98_node82_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 17 6 12 26 21), lower := (rows 17 6 12 26 16), losses := [] }

theorem profile98_node82 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8,18] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8,18] 2 profile98_node82_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8,18] 2 profile98_node82_cert).mp (by decide +kernel))

def profile98_node83_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 6 12 28 19), lower := (rows 17 6 12 28 16), losses := [] }

theorem profile98_node83 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8,20] 2 profile98_node83_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8,20] 2 profile98_node83_cert).mp (by decide +kernel))

def profile98_node80_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node80 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8] 2 (by decide) (choices 2) [17,18,20] profile98_node80_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,8] (choices 2) [17,18,20] profile98_node80_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node81
  · exact profile98_node82
  · exact profile98_node83

def profile98_node85_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 6 20 11 28), lower := (rows 17 6 20 11 16), losses := [{ target := 2, region := (rows 21 2 0 10 16), good := (rows 17 11 17 11 17) }] }

theorem profile98_node85 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16,3] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16,3] 2 profile98_node85_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16,3] 2 profile98_node85_cert).mp (by decide +kernel))

def profile98_node86_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 6 20 13 26), lower := (rows 17 6 20 13 16), losses := [] }

theorem profile98_node86 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16,5] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16,5] 2 profile98_node86_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16,5] 2 profile98_node86_cert).mp (by decide +kernel))

def profile98_node87_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 6 20 14 25), lower := (rows 17 6 20 14 16), losses := [] }

theorem profile98_node87 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16,6] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16,6] 2 profile98_node87_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16,6] 2 profile98_node87_cert).mp (by decide +kernel))

def profile98_node84_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node84 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16] 2 (by decide) (choices 2) [3,5,6] profile98_node84_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4,16] (choices 2) [3,5,6] profile98_node84_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node85
  · exact profile98_node86
  · exact profile98_node87

def profile98_node73_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node73 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4] 2 (by decide) (choices 1) [1,2,8,16] profile98_node73_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,4] (choices 1) [1,2,8,16] profile98_node73_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile98_node74
  · exact profile98_node77
  · exact profile98_node80
  · exact profile98_node84

def profile98_node90_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 10 5 28 22), lower := (rows 17 10 5 28 16), losses := [] }

theorem profile98_node90 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,1,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,1,20] 2 profile98_node90_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,1,20] 2 profile98_node90_cert).mp (by decide +kernel))

def profile98_node89_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node89 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,1] 2 (by decide) (choices 2) [20] profile98_node89_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,1] (choices 2) [20] profile98_node89_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node90

def profile98_node92_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 10 6 28 21), lower := (rows 17 10 6 28 16), losses := [] }

theorem profile98_node92 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,2,20] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,2,20] 2 profile98_node92_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,2,20] 2 profile98_node92_cert).mp (by decide +kernel))

def profile98_node91_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node91 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,2] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,2] 2 (by decide) (choices 2) [20] profile98_node91_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,2] (choices 2) [20] profile98_node91_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node92

def profile98_node94_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 10 20 13 22), lower := (rows 17 10 20 13 16), losses := [] }

theorem profile98_node94 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,16,5] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,16,5] 2 profile98_node94_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,16,5] 2 profile98_node94_cert).mp (by decide +kernel))

def profile98_node95_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 10 20 14 21), lower := (rows 17 10 20 14 16), losses := [] }

theorem profile98_node95 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,16,6] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,16,6] 2 profile98_node95_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,16,6] 2 profile98_node95_cert).mp (by decide +kernel))

def profile98_node93_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node93 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,16] 2 (by decide) (choices 2) [5,6] profile98_node93_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8,16] (choices 2) [5,6] profile98_node93_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile98_node94
  · exact profile98_node95

def profile98_node88_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node88 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8] 2 (by decide) (choices 1) [1,2,16] profile98_node88_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,8] (choices 1) [1,2,16] profile98_node88_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node89
  · exact profile98_node91
  · exact profile98_node93

def profile98_node98_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 18 5 14 28), lower := (rows 17 18 5 14 16), losses := [] }

theorem profile98_node98 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,1,6] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,1,6] 2 profile98_node98_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,1,6] 2 profile98_node98_cert).mp (by decide +kernel))

def profile98_node97_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node97 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,1] 2 (by decide) (choices 2) [6] profile98_node97_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,1] (choices 2) [6] profile98_node97_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node98

def profile98_node100_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 18 6 13 28), lower := (rows 17 18 6 13 16), losses := [] }

theorem profile98_node100 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,2,5] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,2,5] 2 profile98_node100_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,2,5] 2 profile98_node100_cert).mp (by decide +kernel))

def profile98_node99_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node99 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,2] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,2] 2 (by decide) (choices 2) [5] profile98_node99_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,2] (choices 2) [5] profile98_node99_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node100

def profile98_node102_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 18 12 13 22), lower := (rows 17 18 12 13 16), losses := [] }

theorem profile98_node102 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,8,5] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,8,5] 2 profile98_node102_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,8,5] 2 profile98_node102_cert).mp (by decide +kernel))

def profile98_node103_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 18 12 14 21), lower := (rows 17 18 12 14 16), losses := [] }

theorem profile98_node103 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,8,6] 2 :=
  bound_sound (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,8,6] 2 profile98_node103_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,8,6] 2 profile98_node103_cert).mp (by decide +kernel))

def profile98_node101_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node101 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,8] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,8] 2 (by decide) (choices 2) [5,6] profile98_node101_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16,8] (choices 2) [5,6] profile98_node101_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile98_node102
  · exact profile98_node103

def profile98_node96_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node96 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16] 2 (by decide) (choices 1) [1,2,8] profile98_node96_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16,16] (choices 1) [1,2,8] profile98_node96_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile98_node97
  · exact profile98_node99
  · exact profile98_node101

def profile98_node65_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node65 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16] 2 (by decide) (choices 1) [1,4,8,16] profile98_node65_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [16] (choices 1) [1,4,8,16] profile98_node65_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile98_node66
  · exact profile98_node73
  · exact profile98_node88
  · exact profile98_node96

def profile98_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node0 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [] 2 := by
  apply routed_branch (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [] 2 (by decide) (choices 1) [2,4,8,16] profile98_node0_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [] (choices 1) [2,4,8,16] profile98_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile98_node1
  · exact profile98_node19
  · exact profile98_node48
  · exact profile98_node65

theorem profile98 : Upper (D (n:=5) [9,9,10,17,18]) (R (n:=5) [9,9,10,17,18]) [] 2 := profile98_node0

def profile99_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 3 6 20 28 21), lower := (rows 3 6 20 28 16), losses := [] }

theorem profile99_node4 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2,4,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2,4,16,20] 2 profile99_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2,4,16,20] 2 profile99_node4_cert).mp (by decide +kernel))

def profile99_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node3 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2,4,16] 2 (by decide) (choices 2) [20] profile99_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2,4,16] (choices 2) [20] profile99_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node4

def profile99_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node2 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2,4] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2,4] 2 (by decide) (choices 1) [16] profile99_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2,4] (choices 1) [16] profile99_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node3

def profile99_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node1 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2] 2 (by decide) (choices 1) [4] profile99_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [2] (choices 1) [4] profile99_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node2

def profile99_node8_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 5 3 20 28 22), lower := (rows 5 3 20 28 16), losses := [] }

theorem profile99_node8 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,1,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,1,16,20] 2 profile99_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,1,16,20] 2 profile99_node8_cert).mp (by decide +kernel))

def profile99_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node7 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,1,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,1,16] 2 (by decide) (choices 2) [20] profile99_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,1,16] (choices 2) [20] profile99_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node8

def profile99_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node6 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,1] 2 (by decide) (choices 1) [16] profile99_node6_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,1] (choices 1) [16] profile99_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node7

def profile99_node11_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 6 20 25 22), lower := (rows 5 6 20 25 16), losses := [] }

theorem profile99_node11 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16,17] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16,17] 2 profile99_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16,17] 2 profile99_node11_cert).mp (by decide +kernel))

def profile99_node12_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 6 20 26 21), lower := (rows 5 6 20 26 16), losses := [] }

theorem profile99_node12 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16,18] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16,18] 2 profile99_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16,18] 2 profile99_node12_cert).mp (by decide +kernel))

def profile99_node13_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 5 6 20 28 19), lower := (rows 5 6 20 28 16), losses := [] }

theorem profile99_node13 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16,20] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16,20] 2 profile99_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16,20] 2 profile99_node13_cert).mp (by decide +kernel))

def profile99_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node10 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16] 2 (by decide) (choices 2) [17,18,20] profile99_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4,16] (choices 2) [17,18,20] profile99_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile99_node11
  · exact profile99_node12
  · exact profile99_node13

def profile99_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node9 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4] 2 (by decide) (choices 1) [16] profile99_node9_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,4] (choices 1) [16] profile99_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node10

def profile99_node16_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 5 18 5 28 22), lower := (rows 5 18 5 28 16), losses := [] }

theorem profile99_node16 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,1,20] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,1,20] 2 profile99_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,1,20] 2 profile99_node16_cert).mp (by decide +kernel))

def profile99_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node15 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,1] 2 (by decide) (choices 2) [20] profile99_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,1] (choices 2) [20] profile99_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node16

def profile99_node18_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 5 18 6 28 21), lower := (rows 5 18 6 28 16), losses := [] }

theorem profile99_node18 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,2,20] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,2,20] 2 profile99_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,2,20] 2 profile99_node18_cert).mp (by decide +kernel))

def profile99_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node17 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,2] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,2] 2 (by decide) (choices 2) [20] profile99_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,2] (choices 2) [20] profile99_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node18

def profile99_node20_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 5 18 20 13 22), lower := (rows 5 18 20 13 16), losses := [] }

theorem profile99_node20 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,16,5] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,16,5] 2 profile99_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,16,5] 2 profile99_node20_cert).mp (by decide +kernel))

def profile99_node21_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 5 18 20 14 21), lower := (rows 5 18 20 14 16), losses := [] }

theorem profile99_node21 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,16,6] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,16,6] 2 profile99_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,16,6] 2 profile99_node21_cert).mp (by decide +kernel))

def profile99_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node19 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,16] 2 (by decide) (choices 2) [5,6] profile99_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16,16] (choices 2) [5,6] profile99_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile99_node20
  · exact profile99_node21

def profile99_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node14 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16] 2 (by decide) (choices 1) [1,2,16] profile99_node14_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4,16] (choices 1) [1,2,16] profile99_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile99_node15
  · exact profile99_node17
  · exact profile99_node19

def profile99_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node5 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4] 2 (by decide) (choices 1) [1,4,16] profile99_node5_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [4] (choices 1) [1,4,16] profile99_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile99_node6
  · exact profile99_node9
  · exact profile99_node14

def profile99_node25_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 6 5 28 22), lower := (rows 17 6 5 28 16), losses := [] }

theorem profile99_node25 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,1,20] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,1,20] 2 profile99_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,1,20] 2 profile99_node25_cert).mp (by decide +kernel))

def profile99_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node24 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,1] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,1] 2 (by decide) (choices 2) [20] profile99_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,1] (choices 2) [20] profile99_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node25

def profile99_node27_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 17 6 6 28 21), lower := (rows 17 6 6 28 16), losses := [] }

theorem profile99_node27 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,2,20] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,2,20] 2 profile99_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,2,20] 2 profile99_node27_cert).mp (by decide +kernel))

def profile99_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node26 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,2] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,2] 2 (by decide) (choices 2) [20] profile99_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,2] (choices 2) [20] profile99_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node27

def profile99_node29_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 6 20 13 22), lower := (rows 17 6 20 13 16), losses := [] }

theorem profile99_node29 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,16,5] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,16,5] 2 profile99_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,16,5] 2 profile99_node29_cert).mp (by decide +kernel))

def profile99_node30_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 6 20 14 21), lower := (rows 17 6 20 14 16), losses := [] }

theorem profile99_node30 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,16,6] 2 :=
  bound_sound (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,16,6] 2 profile99_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,16,6] 2 profile99_node30_cert).mp (by decide +kernel))

def profile99_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node28 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,16] 2 (by decide) (choices 2) [5,6] profile99_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4,16] (choices 2) [5,6] profile99_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile99_node29
  · exact profile99_node30

def profile99_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node23 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4] 2 (by decide) (choices 1) [1,2,16] profile99_node23_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16,4] (choices 1) [1,2,16] profile99_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile99_node24
  · exact profile99_node26
  · exact profile99_node28

def profile99_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node22 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16] 2 (by decide) (choices 1) [4] profile99_node22_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [16] (choices 1) [4] profile99_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node23

def profile99_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node0 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [] 2 := by
  apply routed_branch (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [] 2 (by decide) (choices 1) [2,4,16] profile99_node0_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [] (choices 1) [2,4,16] profile99_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile99_node1
  · exact profile99_node5
  · exact profile99_node22

theorem profile99 : Upper (D (n:=5) [9,9,11,16,18]) (R (n:=5) [9,9,11,16,18]) [] 2 := profile99_node0

def profile100_node0_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 31 31 31 31 31), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile100_node0 : Upper (D (n:=5) [9,9,11,17,17]) (R (n:=5) [9,9,11,17,17]) [] 2 :=
  bound_sound (D (n:=5) [9,9,11,17,17]) (R (n:=5) [9,9,11,17,17]) [] 2 profile100_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,11,17,17]) (R (n:=5) [9,9,11,17,17]) [] 2 profile100_node0_cert).mp (by decide +kernel))

theorem profile100 : Upper (D (n:=5) [9,9,11,17,17]) (R (n:=5) [9,9,11,17,17]) [] 2 := profile100_node0

def profile101_node0_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 23 23 23 31 23), lower := (rows 1 2 4 8 16), losses := [] }

theorem profile101_node0 : Upper (D (n:=5) [9,9,12,16,17]) (R (n:=5) [9,9,12,16,17]) [] 2 :=
  bound_sound (D (n:=5) [9,9,12,16,17]) (R (n:=5) [9,9,12,16,17]) [] 2 profile101_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,9,12,16,17]) (R (n:=5) [9,9,12,16,17]) [] 2 profile101_node0_cert).mp (by decide +kernel))

theorem profile101 : Upper (D (n:=5) [9,9,12,16,17]) (R (n:=5) [9,9,12,16,17]) [] 2 := profile101_node0

def profile102_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 0), upper := (rows 3 3 12 12 30), lower := (rows 3 3 12 12 30), losses := [] }

theorem profile102_node5 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1,8,4,14] 2 :=
  bound_sound (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1,8,4,14] 2 profile102_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1,8,4,14] 2 profile102_node5_cert).mp (by decide +kernel))

def profile102_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node4 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1,8,4] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1,8,4] 2 (by decide) (choices 3) [14] profile102_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1,8,4] (choices 3) [14] profile102_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile102_node5

def profile102_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node3 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1,8] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1,8] 2 (by decide) (choices 1) [4] profile102_node3_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1,8] (choices 1) [4] profile102_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile102_node4

def profile102_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node2 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1] 2 (by decide) (choices 1) [8] profile102_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,1] (choices 1) [8] profile102_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile102_node3

def profile102_node9_cert : Bound 5 := { allowed := (rows 0 0 0 0 0), upper := (rows 3 6 12 9 30), lower := (rows 3 6 12 9 30), losses := [] }

theorem profile102_node9 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,1,14] 2 :=
  bound_sound (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,1,14] 2 profile102_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,1,14] 2 profile102_node9_cert).mp (by decide +kernel))

def profile102_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node8 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,1] 2 (by decide) (choices 3) [14] profile102_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,1] (choices 3) [14] profile102_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile102_node9

def profile102_node11_cert : Bound 5 := { allowed := (rows 0 0 0 0 2), upper := (rows 3 6 12 10 29), lower := (rows 3 6 12 10 29), losses := [] }

theorem profile102_node11 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,2,13] 2 :=
  bound_sound (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,2,13] 2 profile102_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,2,13] 2 profile102_node11_cert).mp (by decide +kernel))

def profile102_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node10 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,2] 2 (by decide) (choices 3) [13] profile102_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,2] (choices 3) [13] profile102_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile102_node11

def profile102_node13_cert : Bound 5 := { allowed := (rows 0 0 0 0 4), upper := (rows 3 6 12 12 27), lower := (rows 3 6 12 12 27), losses := [] }

theorem profile102_node13 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,4,11] 2 :=
  bound_sound (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,4,11] 2 profile102_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,4,11] 2 profile102_node13_cert).mp (by decide +kernel))

def profile102_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node12 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,4] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,4] 2 (by decide) (choices 3) [11] profile102_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8,4] (choices 3) [11] profile102_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile102_node13

def profile102_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node7 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8] 2 (by decide) (choices 1) [1,2,4] profile102_node7_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4,8] (choices 1) [1,2,4] profile102_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile102_node8
  · exact profile102_node10
  · exact profile102_node12

def profile102_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node6 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4] 2 (by decide) (choices 1) [8] profile102_node6_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2,4] (choices 1) [8] profile102_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile102_node7

def profile102_node1_route : Route 5 := (fun mask => match mask with | 8 => (4,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile102_node1 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2] 2 (by decide) (choices 1) [1,4] profile102_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [2] (choices 1) [1,4] profile102_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile102_node2
  · exact profile102_node6

def profile102_node0_route : Route 5 := (fun mask => match mask with | 4 => (2,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 8 => (2,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile102_node0 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [] 2 (by decide) (choices 1) [2] profile102_node0_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [] (choices 1) [2] profile102_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile102_node1

theorem profile102 : Upper (D (n:=5) [9,10,10,10,24]) (R (n:=5) [9,10,10,10,24]) [] 2 := profile102_node0

def profile103_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 3 3 20 28 22), lower := (rows 3 3 20 28 16), losses := [{ target := 1, region := (rows 1 0 28 28 16), good := (rows 1 1 28 28 28) }] }

theorem profile103_node4 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,1,16,20] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,1,16,20] 2 profile103_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,1,16,20] 2 profile103_node4_cert).mp (by decide +kernel))

def profile103_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node3 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,1,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,1,16] 2 (by decide) (choices 2) [20] profile103_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,1,16] (choices 2) [20] profile103_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node4

def profile103_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node2 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,1] 2 (by decide) (choices 1) [16] profile103_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,1] (choices 1) [16] profile103_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node3

def profile103_node8_cert : Bound 5 := { allowed := (rows 0 0 0 6 0), upper := (rows 3 6 20 25 22), lower := (rows 3 6 20 25 22), losses := [] }

theorem profile103_node8 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,17,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,17,6] 2 profile103_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,17,6] 2 profile103_node8_cert).mp (by decide +kernel))

def profile103_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node7 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,17] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,17] 2 (by decide) (choices 2) [6] profile103_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,17] (choices 2) [6] profile103_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node8

def profile103_node9_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 3 6 20 26 21), lower := (rows 3 6 20 26 16), losses := [{ target := 1, region := (rows 1 0 29 8 17), good := (rows 21 4 20 28 20) }] }

theorem profile103_node9 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,18] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,18] 2 profile103_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,18] 2 profile103_node9_cert).mp (by decide +kernel))

def profile103_node10_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 3 6 20 28 19), lower := (rows 3 6 20 28 16), losses := [{ target := 1, region := (rows 1 0 28 28 16), good := (rows 1 12 28 28 28) }] }

theorem profile103_node10 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,20] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,20] 2 profile103_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16,20] 2 profile103_node10_cert).mp (by decide +kernel))

def profile103_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node6 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16] 2 (by decide) (choices 2) [17,18,20] profile103_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4,16] (choices 2) [17,18,20] profile103_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile103_node7
  · exact profile103_node9
  · exact profile103_node10

def profile103_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node5 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4] 2 (by decide) (choices 1) [16] profile103_node5_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,4] (choices 1) [16] profile103_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node6

def profile103_node14_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 3 18 5 28 22), lower := (rows 3 18 5 28 22), losses := [] }

theorem profile103_node14 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,1,20,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,1,20,6] 2 profile103_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,1,20,6] 2 profile103_node14_cert).mp (by decide +kernel))

def profile103_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node13 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,1,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,1,20] 2 (by decide) (choices 2) [6] profile103_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,1,20] (choices 2) [6] profile103_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node14

def profile103_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node12 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,1] 2 (by decide) (choices 2) [20] profile103_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,1] (choices 2) [20] profile103_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node13

def profile103_node17_cert : Bound 5 := { allowed := (rows 0 0 0 2 2), upper := (rows 3 18 6 28 21), lower := (rows 3 18 6 28 21), losses := [] }

theorem profile103_node17 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,2,20,5] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,2,20,5] 2 profile103_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,2,20,5] 2 profile103_node17_cert).mp (by decide +kernel))

def profile103_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node16 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,2,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,2,20] 2 (by decide) (choices 2) [5] profile103_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,2,20] (choices 2) [5] profile103_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node17

def profile103_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node15 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,2] 2 (by decide) (choices 2) [20] profile103_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,2] (choices 2) [20] profile103_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node16

def profile103_node20_cert : Bound 5 := { allowed := (rows 0 0 0 18 0), upper := (rows 3 18 20 13 22), lower := (rows 3 18 20 13 22), losses := [] }

theorem profile103_node20 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16,5,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16,5,6] 2 profile103_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16,5,6] 2 profile103_node20_cert).mp (by decide +kernel))

def profile103_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node19 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16,5] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16,5] 2 (by decide) (choices 2) [6] profile103_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16,5] (choices 2) [6] profile103_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node20

def profile103_node21_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 3 18 20 14 21), lower := (rows 3 18 20 14 16), losses := [{ target := 1, region := (rows 1 0 23 8 17), good := (rows 21 20 20 12 20) }] }

theorem profile103_node21 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16,6] 2 profile103_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16,6] 2 profile103_node21_cert).mp (by decide +kernel))

def profile103_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node18 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16] 2 (by decide) (choices 2) [5,6] profile103_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16,16] (choices 2) [5,6] profile103_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile103_node19
  · exact profile103_node21

def profile103_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node11 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16] 2 (by decide) (choices 1) [1,2,16] profile103_node11_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2,16] (choices 1) [1,2,16] profile103_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile103_node12
  · exact profile103_node15
  · exact profile103_node18

def profile103_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node1 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2] 2 (by decide) (choices 1) [1,4,16] profile103_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [2] (choices 1) [1,4,16] profile103_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile103_node2
  · exact profile103_node5
  · exact profile103_node11

def profile103_node26_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 17 3 6 28 22), lower := (rows 17 3 6 28 22), losses := [] }

theorem profile103_node26 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,2,20,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,2,20,6] 2 profile103_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,2,20,6] 2 profile103_node26_cert).mp (by decide +kernel))

def profile103_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node25 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,2,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,2,20] 2 (by decide) (choices 2) [6] profile103_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,2,20] (choices 2) [6] profile103_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node26

def profile103_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node24 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,2] 2 (by decide) (choices 2) [20] profile103_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,2] (choices 2) [20] profile103_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node25

def profile103_node29_cert : Bound 5 := { allowed := (rows 0 0 0 16 0), upper := (rows 17 3 20 14 22), lower := (rows 17 3 20 14 22), losses := [] }

theorem profile103_node29 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,16,6,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,16,6,6] 2 profile103_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,16,6,6] 2 profile103_node29_cert).mp (by decide +kernel))

def profile103_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node28 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,16,6] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,16,6] 2 (by decide) (choices 2) [6] profile103_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,16,6] (choices 2) [6] profile103_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node29

def profile103_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node27 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,16] 2 (by decide) (choices 2) [6] profile103_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1,16] (choices 2) [6] profile103_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node28

def profile103_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node23 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1] 2 (by decide) (choices 1) [2,16] profile103_node23_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,1] (choices 1) [2,16] profile103_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile103_node24
  · exact profile103_node27

def profile103_node33_cert : Bound 5 := { allowed := (rows 0 0 0 4 0), upper := (rows 17 6 5 26 22), lower := (rows 17 6 5 26 22), losses := [] }

theorem profile103_node33 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,1,18,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,1,18,6] 2 profile103_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,1,18,6] 2 profile103_node33_cert).mp (by decide +kernel))

def profile103_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node32 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,1,18] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,1,18] 2 (by decide) (choices 2) [6] profile103_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,1,18] (choices 2) [6] profile103_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node33

def profile103_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node31 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,1] 2 (by decide) (choices 2) [18] profile103_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,1] (choices 2) [18] profile103_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node32

def profile103_node35_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 17 6 6 25 22), lower := (rows 17 6 6 25 16), losses := [{ target := 1, region := (rows 25 0 4 25 16), good := (rows 25 4 4 25 25) },{ target := 2, region := (rows 25 2 0 25 16), good := (rows 25 2 2 25 25) }] }

theorem profile103_node35 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2,17] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2,17] 2 profile103_node35_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2,17] 2 profile103_node35_cert).mp (by decide +kernel))

def profile103_node36_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 17 6 6 26 21), lower := (rows 17 6 6 26 16), losses := [{ target := 1, region := (rows 31 0 4 8 22), good := (rows 17 21 21 25 17) }] }

theorem profile103_node36 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2,18] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2,18] 2 profile103_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2,18] 2 profile103_node36_cert).mp (by decide +kernel))

def profile103_node37_cert : Bound 5 := { allowed := (rows 0 0 0 2 2), upper := (rows 17 6 6 28 19), lower := (rows 17 6 6 28 16), losses := [{ target := 2, region := (rows 31 2 0 8 22), good := (rows 17 19 19 25 17) }] }

theorem profile103_node37 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2,20] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2,20] 2 profile103_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2,20] 2 profile103_node37_cert).mp (by decide +kernel))

def profile103_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node34 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2] 2 (by decide) (choices 2) [17,18,20] profile103_node34_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,2] (choices 2) [17,18,20] profile103_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile103_node35
  · exact profile103_node36
  · exact profile103_node37

def profile103_node40_cert : Bound 5 := { allowed := (rows 0 0 0 20 0), upper := (rows 17 6 20 11 22), lower := (rows 17 6 20 11 22), losses := [] }

theorem profile103_node40 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16,3,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16,3,6] 2 profile103_node40_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16,3,6] 2 profile103_node40_cert).mp (by decide +kernel))

def profile103_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node39 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16,3] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16,3] 2 (by decide) (choices 2) [6] profile103_node39_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16,3] (choices 2) [6] profile103_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node40

def profile103_node41_cert : Bound 5 := { allowed := (rows 0 0 0 16 2), upper := (rows 17 6 20 14 19), lower := (rows 17 6 20 14 16), losses := [{ target := 2, region := (rows 31 2 0 8 26), good := (rows 17 19 17 27 17) }] }

theorem profile103_node41 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16,6] 2 profile103_node41_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16,6] 2 profile103_node41_cert).mp (by decide +kernel))

def profile103_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node38 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16] 2 (by decide) (choices 2) [3,6] profile103_node38_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4,16] (choices 2) [3,6] profile103_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile103_node39
  · exact profile103_node41

def profile103_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node30 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4] 2 (by decide) (choices 1) [1,2,16] profile103_node30_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,4] (choices 1) [1,2,16] profile103_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile103_node31
  · exact profile103_node34
  · exact profile103_node38

def profile103_node45_cert : Bound 5 := { allowed := (rows 0 0 0 16 0), upper := (rows 17 18 5 14 22), lower := (rows 17 18 5 14 22), losses := [] }

theorem profile103_node45 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,1,6,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,1,6,6] 2 profile103_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,1,6,6] 2 profile103_node45_cert).mp (by decide +kernel))

def profile103_node44_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node44 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,1,6] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,1,6] 2 (by decide) (choices 2) [6] profile103_node44_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,1,6] (choices 2) [6] profile103_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node45

def profile103_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node43 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,1] 2 (by decide) (choices 2) [6] profile103_node43_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,1] (choices 2) [6] profile103_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node44

def profile103_node48_cert : Bound 5 := { allowed := (rows 0 0 0 18 0), upper := (rows 17 18 6 13 22), lower := (rows 17 18 6 13 22), losses := [] }

theorem profile103_node48 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2,5,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2,5,6] 2 profile103_node48_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2,5,6] 2 profile103_node48_cert).mp (by decide +kernel))

def profile103_node47_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node47 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2,5] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2,5] 2 (by decide) (choices 2) [6] profile103_node47_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2,5] (choices 2) [6] profile103_node47_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node48

def profile103_node49_cert : Bound 5 := { allowed := (rows 0 0 0 16 4), upper := (rows 17 18 6 14 21), lower := (rows 17 18 6 14 16), losses := [{ target := 1, region := (rows 31 0 4 8 28), good := (rows 17 17 21 29 17) }] }

theorem profile103_node49 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2,6] 2 profile103_node49_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2,6] 2 profile103_node49_cert).mp (by decide +kernel))

def profile103_node46_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node46 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2] 2 (by decide) (choices 2) [5,6] profile103_node46_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16,2] (choices 2) [5,6] profile103_node46_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile103_node47
  · exact profile103_node49

def profile103_node42_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node42 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16] 2 (by decide) (choices 1) [1,2] profile103_node42_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16,16] (choices 1) [1,2] profile103_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile103_node43
  · exact profile103_node46

def profile103_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node22 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16] 2 (by decide) (choices 1) [1,4,16] profile103_node22_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [16] (choices 1) [1,4,16] profile103_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile103_node23
  · exact profile103_node30
  · exact profile103_node42

def profile103_node0_route : Route 5 := (fun mask => match mask with | 4 => (2,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile103_node0 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [] 2 (by decide) (choices 1) [2,16] profile103_node0_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [] (choices 1) [2,16] profile103_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile103_node1
  · exact profile103_node22

theorem profile103 : Upper (D (n:=5) [9,10,10,16,18]) (R (n:=5) [9,10,10,16,18]) [] 2 := profile103_node0

def profile104_node3_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 3 3 6 28 28), lower := (rows 3 3 6 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 1 1 28 8 16) }] }

theorem profile104_node3 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1,2] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1,2] 2 profile104_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1,2] 2 profile104_node3_cert).mp (by decide +kernel))

def profile104_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 3 3 12 28 22), lower := (rows 3 3 12 28 16), losses := [{ target := 1, region := (rows 1 0 28 24 16), good := (rows 1 1 12 28 28) }] }

theorem profile104_node5 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1,8,20] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1,8,20] 2 profile104_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1,8,20] 2 profile104_node5_cert).mp (by decide +kernel))

def profile104_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node4 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1,8] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1,8] 2 (by decide) (choices 2) [20] profile104_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1,8] (choices 2) [20] profile104_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node5

def profile104_node2_route : Route 5 := (fun mask => match mask with | 16 => (8,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile104_node2 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1] 2 (by decide) (choices 1) [2,8] profile104_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,1] (choices 1) [2,8] profile104_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile104_node3
  · exact profile104_node4

def profile104_node9_cert : Bound 5 := { allowed := (rows 0 0 0 4 2), upper := (rows 3 6 5 26 28), lower := (rows 3 6 5 26 28), losses := [] }

theorem profile104_node9 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,18,12] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,18,12] 2 profile104_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,18,12] 2 profile104_node9_cert).mp (by decide +kernel))

def profile104_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node8 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,18] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,18] 2 (by decide) (choices 2) [12] profile104_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,18] (choices 2) [12] profile104_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node9

def profile104_node11_cert : Bound 5 := { allowed := (rows 0 0 0 2 4), upper := (rows 3 6 5 28 26), lower := (rows 3 6 5 28 26), losses := [] }

theorem profile104_node11 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,20,10] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,20,10] 2 profile104_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,20,10] 2 profile104_node11_cert).mp (by decide +kernel))

def profile104_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node10 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,20] 2 (by decide) (choices 2) [10] profile104_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1,20] (choices 2) [10] profile104_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node11

def profile104_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node7 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1] 2 (by decide) (choices 2) [18,20] profile104_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,1] (choices 2) [18,20] profile104_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile104_node8
  · exact profile104_node10

def profile104_node14_cert : Bound 5 := { allowed := (rows 0 0 0 2 2), upper := (rows 3 6 6 25 28), lower := (rows 3 6 6 25 28), losses := [{ target := 2, region := (rows 7 2 0 24 16), good := (rows 3 3 3 25 25) }] }

theorem profile104_node14 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2,17,12] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2,17,12] 2 profile104_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2,17,12] 2 profile104_node14_cert).mp (by decide +kernel))

def profile104_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node13 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2,17] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2,17] 2 (by decide) (choices 2) [12] profile104_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2,17] (choices 2) [12] profile104_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node14

def profile104_node15_cert : Bound 5 := { allowed := (rows 0 0 0 2 2), upper := (rows 3 6 6 28 25), lower := (rows 3 6 6 28 16), losses := [{ target := 2, region := (rows 7 2 0 8 24), good := (rows 3 3 3 25 16) }] }

theorem profile104_node15 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2,20] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2,20] 2 profile104_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2,20] 2 profile104_node15_cert).mp (by decide +kernel))

def profile104_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node12 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2] 2 (by decide) (choices 2) [17,20] profile104_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,2] (choices 2) [17,20] profile104_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile104_node13
  · exact profile104_node15

def profile104_node18_cert : Bound 5 := { allowed := (rows 0 0 0 6 0), upper := (rows 3 6 12 25 22), lower := (rows 3 6 12 25 22), losses := [] }

theorem profile104_node18 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,17,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,17,6] 2 profile104_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,17,6] 2 profile104_node18_cert).mp (by decide +kernel))

def profile104_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node17 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,17] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,17] 2 (by decide) (choices 2) [6] profile104_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,17] (choices 2) [6] profile104_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node18

def profile104_node20_cert : Bound 5 := { allowed := (rows 0 0 0 4 2), upper := (rows 3 6 12 26 21), lower := (rows 3 6 12 26 21), losses := [] }

theorem profile104_node20 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,18,5] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,18,5] 2 profile104_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,18,5] 2 profile104_node20_cert).mp (by decide +kernel))

def profile104_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node19 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,18] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,18] 2 (by decide) (choices 2) [5] profile104_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,18] (choices 2) [5] profile104_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node20

def profile104_node21_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 3 6 12 28 19), lower := (rows 3 6 12 28 16), losses := [{ target := 1, region := (rows 1 0 28 24 16), good := (rows 1 4 12 28 28) }] }

theorem profile104_node21 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,20] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,20] 2 profile104_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8,20] 2 profile104_node21_cert).mp (by decide +kernel))

def profile104_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node16 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8] 2 (by decide) (choices 2) [17,18,20] profile104_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4,8] (choices 2) [17,18,20] profile104_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile104_node17
  · exact profile104_node19
  · exact profile104_node21

def profile104_node6_route : Route 5 := (fun mask => match mask with | 16 => (8,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile104_node6 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4] 2 (by decide) (choices 1) [1,2,8] profile104_node6_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,4] (choices 1) [1,2,8] profile104_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile104_node7
  · exact profile104_node12
  · exact profile104_node16

def profile104_node25_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 3 10 5 28 22), lower := (rows 3 10 5 28 22), losses := [] }

theorem profile104_node25 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,1,20,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,1,20,6] 2 profile104_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,1,20,6] 2 profile104_node25_cert).mp (by decide +kernel))

def profile104_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node24 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,1,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,1,20] 2 (by decide) (choices 2) [6] profile104_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,1,20] (choices 2) [6] profile104_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node25

def profile104_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node23 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,1] 2 (by decide) (choices 2) [20] profile104_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,1] (choices 2) [20] profile104_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node24

def profile104_node28_cert : Bound 5 := { allowed := (rows 0 0 0 2 2), upper := (rows 3 10 6 28 21), lower := (rows 3 10 6 28 21), losses := [] }

theorem profile104_node28 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,2,20,5] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,2,20,5] 2 profile104_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,2,20,5] 2 profile104_node28_cert).mp (by decide +kernel))

def profile104_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node27 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,2,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,2,20] 2 (by decide) (choices 2) [5] profile104_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,2,20] (choices 2) [5] profile104_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node28

def profile104_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node26 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,2] 2 (by decide) (choices 2) [20] profile104_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,2] (choices 2) [20] profile104_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node27

def profile104_node31_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 3 10 20 13 22), lower := (rows 3 10 20 13 22), losses := [] }

theorem profile104_node31 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16,5,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16,5,6] 2 profile104_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16,5,6] 2 profile104_node31_cert).mp (by decide +kernel))

def profile104_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node30 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16,5] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16,5] 2 (by decide) (choices 2) [6] profile104_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16,5] (choices 2) [6] profile104_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node31

def profile104_node32_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 3 10 20 14 21), lower := (rows 3 10 20 14 16), losses := [] }

theorem profile104_node32 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16,6] 2 profile104_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16,6] 2 profile104_node32_cert).mp (by decide +kernel))

def profile104_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node29 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16] 2 (by decide) (choices 2) [5,6] profile104_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8,16] (choices 2) [5,6] profile104_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile104_node30
  · exact profile104_node32

def profile104_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node22 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8] 2 (by decide) (choices 1) [1,2,16] profile104_node22_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2,8] (choices 1) [1,2,16] profile104_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile104_node23
  · exact profile104_node26
  · exact profile104_node29

def profile104_node1_route : Route 5 := (fun mask => match mask with | 16 => (8,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile104_node1 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2] 2 (by decide) (choices 1) [1,4,8] profile104_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [2] (choices 1) [1,4,8] profile104_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile104_node2
  · exact profile104_node6
  · exact profile104_node22

def profile104_node37_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 9 3 6 28 22), lower := (rows 9 3 6 28 22), losses := [] }

theorem profile104_node37 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,2,20,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,2,20,6] 2 profile104_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,2,20,6] 2 profile104_node37_cert).mp (by decide +kernel))

def profile104_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node36 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,2,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,2,20] 2 (by decide) (choices 2) [6] profile104_node36_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,2,20] (choices 2) [6] profile104_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node37

def profile104_node35_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node35 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,2] 2 (by decide) (choices 2) [20] profile104_node35_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,2] (choices 2) [20] profile104_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node36

def profile104_node39_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 9 3 20 14 22), lower := (rows 9 3 20 14 16), losses := [] }

theorem profile104_node39 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,16,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,16,6] 2 profile104_node39_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,16,6] 2 profile104_node39_cert).mp (by decide +kernel))

def profile104_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node38 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,16] 2 (by decide) (choices 2) [6] profile104_node38_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1,16] (choices 2) [6] profile104_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node39

def profile104_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node34 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1] 2 (by decide) (choices 1) [2,16] profile104_node34_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,1] (choices 1) [2,16] profile104_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile104_node35
  · exact profile104_node38

def profile104_node43_cert : Bound 5 := { allowed := (rows 0 0 0 4 0), upper := (rows 9 6 5 26 22), lower := (rows 9 6 5 26 22), losses := [] }

theorem profile104_node43 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,1,18,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,1,18,6] 2 profile104_node43_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,1,18,6] 2 profile104_node43_cert).mp (by decide +kernel))

def profile104_node42_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node42 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,1,18] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,1,18] 2 (by decide) (choices 2) [6] profile104_node42_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,1,18] (choices 2) [6] profile104_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node43

def profile104_node41_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node41 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,1] 2 (by decide) (choices 2) [18] profile104_node41_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,1] (choices 2) [18] profile104_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node42

def profile104_node45_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 9 6 6 25 22), lower := (rows 9 6 6 25 16), losses := [{ target := 1, region := (rows 25 0 4 24 16), good := (rows 9 4 4 25 25) },{ target := 2, region := (rows 25 2 0 24 16), good := (rows 9 2 2 25 25) }] }

theorem profile104_node45 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,17] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,17] 2 profile104_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,17] 2 profile104_node45_cert).mp (by decide +kernel))

def profile104_node47_cert : Bound 5 := { allowed := (rows 0 0 0 4 2), upper := (rows 9 6 6 26 21), lower := (rows 9 6 6 26 21), losses := [] }

theorem profile104_node47 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,18,5] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,18,5] 2 profile104_node47_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,18,5] 2 profile104_node47_cert).mp (by decide +kernel))

def profile104_node46_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node46 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,18] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,18] 2 (by decide) (choices 2) [5] profile104_node46_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,18] (choices 2) [5] profile104_node46_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node47

def profile104_node49_cert : Bound 5 := { allowed := (rows 0 0 0 2 4), upper := (rows 9 6 6 28 19), lower := (rows 9 6 6 28 19), losses := [] }

theorem profile104_node49 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,20,3] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,20,3] 2 profile104_node49_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,20,3] 2 profile104_node49_cert).mp (by decide +kernel))

def profile104_node48_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node48 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,20] 2 (by decide) (choices 2) [3] profile104_node48_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2,20] (choices 2) [3] profile104_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node49

def profile104_node44_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node44 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2] 2 (by decide) (choices 2) [17,18,20] profile104_node44_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,2] (choices 2) [17,18,20] profile104_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile104_node45
  · exact profile104_node46
  · exact profile104_node48

def profile104_node51_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 9 6 20 11 22), lower := (rows 9 6 20 11 16), losses := [{ target := 2, region := (rows 11 2 0 10 16), good := (rows 9 11 16 11 16) }] }

theorem profile104_node51 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,16,3] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,16,3] 2 profile104_node51_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,16,3] 2 profile104_node51_cert).mp (by decide +kernel))

def profile104_node52_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 9 6 20 14 19), lower := (rows 9 6 20 14 16), losses := [] }

theorem profile104_node52 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,16,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,16,6] 2 profile104_node52_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,16,6] 2 profile104_node52_cert).mp (by decide +kernel))

def profile104_node50_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node50 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,16] 2 (by decide) (choices 2) [3,6] profile104_node50_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4,16] (choices 2) [3,6] profile104_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile104_node51
  · exact profile104_node52

def profile104_node40_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node40 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4] 2 (by decide) (choices 1) [1,2,16] profile104_node40_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,4] (choices 1) [1,2,16] profile104_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile104_node41
  · exact profile104_node44
  · exact profile104_node50

def profile104_node55_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 9 18 5 14 22), lower := (rows 9 18 5 14 16), losses := [] }

theorem profile104_node55 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,1,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,1,6] 2 profile104_node55_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,1,6] 2 profile104_node55_cert).mp (by decide +kernel))

def profile104_node54_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node54 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,1] 2 (by decide) (choices 2) [6] profile104_node54_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,1] (choices 2) [6] profile104_node54_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node55

def profile104_node57_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 9 18 6 13 22), lower := (rows 9 18 6 13 16), losses := [{ target := 1, region := (rows 13 0 4 12 16), good := (rows 9 16 13 13 16) }] }

theorem profile104_node57 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,2,5] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,2,5] 2 profile104_node57_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,2,5] 2 profile104_node57_cert).mp (by decide +kernel))

def profile104_node58_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 9 18 6 14 21), lower := (rows 9 18 6 14 16), losses := [] }

theorem profile104_node58 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,2,6] 2 :=
  bound_sound (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,2,6] 2 profile104_node58_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,2,6] 2 profile104_node58_cert).mp (by decide +kernel))

def profile104_node56_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node56 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,2] 2 (by decide) (choices 2) [5,6] profile104_node56_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16,2] (choices 2) [5,6] profile104_node56_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile104_node57
  · exact profile104_node58

def profile104_node53_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node53 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16] 2 (by decide) (choices 1) [1,2] profile104_node53_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8,16] (choices 1) [1,2] profile104_node53_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile104_node54
  · exact profile104_node56

def profile104_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node33 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8] 2 (by decide) (choices 1) [1,4,16] profile104_node33_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [8] (choices 1) [1,4,16] profile104_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile104_node34
  · exact profile104_node40
  · exact profile104_node53

def profile104_node0_route : Route 5 := (fun mask => match mask with | 4 => (2,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 16 => (8,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile104_node0 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [] 2 := by
  apply routed_branch (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [] 2 (by decide) (choices 1) [2,8] profile104_node0_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [] (choices 1) [2,8] profile104_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile104_node1
  · exact profile104_node33

theorem profile104 : Upper (D (n:=5) [9,10,10,17,17]) (R (n:=5) [9,10,10,17,17]) [] 2 := profile104_node0

def profile105_node5_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 3 6 5 28 22), lower := (rows 3 6 5 28 22), losses := [] }

theorem profile105_node5 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,1,20,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,1,20,6] 2 profile105_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,1,20,6] 2 profile105_node5_cert).mp (by decide +kernel))

def profile105_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node4 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,1,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,1,20] 2 (by decide) (choices 2) [6] profile105_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,1,20] (choices 2) [6] profile105_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node5

def profile105_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node3 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,1] 2 (by decide) (choices 2) [20] profile105_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,1] (choices 2) [20] profile105_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node4

def profile105_node8_cert : Bound 5 := { allowed := (rows 0 0 0 2 2), upper := (rows 3 6 6 28 21), lower := (rows 3 6 6 28 21), losses := [] }

theorem profile105_node8 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,2,20,5] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,2,20,5] 2 profile105_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,2,20,5] 2 profile105_node8_cert).mp (by decide +kernel))

def profile105_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node7 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,2,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,2,20] 2 (by decide) (choices 2) [5] profile105_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,2,20] (choices 2) [5] profile105_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node8

def profile105_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node6 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,2] 2 (by decide) (choices 2) [20] profile105_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,2] (choices 2) [20] profile105_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node7

def profile105_node11_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 3 6 20 13 22), lower := (rows 3 6 20 13 22), losses := [] }

theorem profile105_node11 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16,5,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16,5,6] 2 profile105_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16,5,6] 2 profile105_node11_cert).mp (by decide +kernel))

def profile105_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node10 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16,5] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16,5] 2 (by decide) (choices 2) [6] profile105_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16,5] (choices 2) [6] profile105_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node11

def profile105_node12_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 3 6 20 14 21), lower := (rows 3 6 20 14 16), losses := [] }

theorem profile105_node12 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16,6] 2 profile105_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16,6] 2 profile105_node12_cert).mp (by decide +kernel))

def profile105_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node9 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16] 2 (by decide) (choices 2) [5,6] profile105_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4,16] (choices 2) [5,6] profile105_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile105_node10
  · exact profile105_node12

def profile105_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node2 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4] 2 (by decide) (choices 1) [1,2,16] profile105_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2,4] (choices 1) [1,2,16] profile105_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile105_node3
  · exact profile105_node6
  · exact profile105_node9

def profile105_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node1 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2] 2 (by decide) (choices 1) [4] profile105_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [2] (choices 1) [4] profile105_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node2

def profile105_node17_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 5 3 6 28 22), lower := (rows 5 3 6 28 22), losses := [] }

theorem profile105_node17 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,2,20,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,2,20,6] 2 profile105_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,2,20,6] 2 profile105_node17_cert).mp (by decide +kernel))

def profile105_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node16 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,2,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,2,20] 2 (by decide) (choices 2) [6] profile105_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,2,20] (choices 2) [6] profile105_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node17

def profile105_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node15 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,2] 2 (by decide) (choices 2) [20] profile105_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,2] (choices 2) [20] profile105_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node16

def profile105_node19_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 5 3 20 14 22), lower := (rows 5 3 20 14 16), losses := [] }

theorem profile105_node19 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,16,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,16,6] 2 profile105_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,16,6] 2 profile105_node19_cert).mp (by decide +kernel))

def profile105_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node18 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,16] 2 (by decide) (choices 2) [6] profile105_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1,16] (choices 2) [6] profile105_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node19

def profile105_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node14 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1] 2 (by decide) (choices 1) [2,16] profile105_node14_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,1] (choices 1) [2,16] profile105_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile105_node15
  · exact profile105_node18

def profile105_node23_cert : Bound 5 := { allowed := (rows 0 0 0 4 0), upper := (rows 5 6 5 26 22), lower := (rows 5 6 5 26 22), losses := [] }

theorem profile105_node23 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,1,18,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,1,18,6] 2 profile105_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,1,18,6] 2 profile105_node23_cert).mp (by decide +kernel))

def profile105_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node22 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,1,18] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,1,18] 2 (by decide) (choices 2) [6] profile105_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,1,18] (choices 2) [6] profile105_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node23

def profile105_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node21 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,1] 2 (by decide) (choices 2) [18] profile105_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,1] (choices 2) [18] profile105_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node22

def profile105_node26_cert : Bound 5 := { allowed := (rows 0 0 0 6 0), upper := (rows 5 6 6 25 22), lower := (rows 5 6 6 25 22), losses := [] }

theorem profile105_node26 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,17,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,17,6] 2 profile105_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,17,6] 2 profile105_node26_cert).mp (by decide +kernel))

def profile105_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node25 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,17] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,17] 2 (by decide) (choices 2) [6] profile105_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,17] (choices 2) [6] profile105_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node26

def profile105_node27_cert : Bound 5 := { allowed := (rows 0 0 0 4 4), upper := (rows 5 6 6 26 21), lower := (rows 5 6 6 26 16), losses := [{ target := 1, region := (rows 7 0 4 8 23), good := (rows 21 21 21 25 16) }] }

theorem profile105_node27 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,18] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,18] 2 profile105_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,18] 2 profile105_node27_cert).mp (by decide +kernel))

def profile105_node29_cert : Bound 5 := { allowed := (rows 0 0 0 2 4), upper := (rows 5 6 6 28 19), lower := (rows 5 6 6 28 19), losses := [] }

theorem profile105_node29 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,20,3] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,20,3] 2 profile105_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,20,3] 2 profile105_node29_cert).mp (by decide +kernel))

def profile105_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node28 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,20] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,20] 2 (by decide) (choices 2) [3] profile105_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2,20] (choices 2) [3] profile105_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node29

def profile105_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node24 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2] 2 (by decide) (choices 2) [17,18,20] profile105_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,2] (choices 2) [17,18,20] profile105_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile105_node25
  · exact profile105_node27
  · exact profile105_node28

def profile105_node32_cert : Bound 5 := { allowed := (rows 0 0 0 4 0), upper := (rows 5 6 20 11 22), lower := (rows 5 6 20 11 22), losses := [] }

theorem profile105_node32 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16,3,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16,3,6] 2 profile105_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16,3,6] 2 profile105_node32_cert).mp (by decide +kernel))

def profile105_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node31 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16,3] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16,3] 2 (by decide) (choices 2) [6] profile105_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16,3] (choices 2) [6] profile105_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node32

def profile105_node33_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 5 6 20 14 19), lower := (rows 5 6 20 14 16), losses := [] }

theorem profile105_node33 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16,6] 2 profile105_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16,6] 2 profile105_node33_cert).mp (by decide +kernel))

def profile105_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node30 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16] 2 (by decide) (choices 2) [3,6] profile105_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4,16] (choices 2) [3,6] profile105_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile105_node31
  · exact profile105_node33

def profile105_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node20 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4] 2 (by decide) (choices 1) [1,2,16] profile105_node20_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,4] (choices 1) [1,2,16] profile105_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile105_node21
  · exact profile105_node24
  · exact profile105_node30

def profile105_node36_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 5 18 5 14 22), lower := (rows 5 18 5 14 16), losses := [] }

theorem profile105_node36 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,1,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,1,6] 2 profile105_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,1,6] 2 profile105_node36_cert).mp (by decide +kernel))

def profile105_node35_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node35 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,1] 2 (by decide) (choices 2) [6] profile105_node35_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,1] (choices 2) [6] profile105_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node36

def profile105_node38_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 5 18 6 13 22), lower := (rows 5 18 6 13 16), losses := [{ target := 1, region := (rows 13 0 4 13 16), good := (rows 13 16 13 13 16) }] }

theorem profile105_node38 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,2,5] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,2,5] 2 profile105_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,2,5] 2 profile105_node38_cert).mp (by decide +kernel))

def profile105_node39_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 5 18 6 14 21), lower := (rows 5 18 6 14 16), losses := [] }

theorem profile105_node39 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,2,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,2,6] 2 profile105_node39_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,2,6] 2 profile105_node39_cert).mp (by decide +kernel))

def profile105_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node37 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,2] 2 (by decide) (choices 2) [5,6] profile105_node37_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16,2] (choices 2) [5,6] profile105_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile105_node38
  · exact profile105_node39

def profile105_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node34 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16] 2 (by decide) (choices 1) [1,2] profile105_node34_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4,16] (choices 1) [1,2] profile105_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile105_node35
  · exact profile105_node37

def profile105_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node13 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4] 2 (by decide) (choices 1) [1,4,16] profile105_node13_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [4] (choices 1) [1,4,16] profile105_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile105_node14
  · exact profile105_node20
  · exact profile105_node34

def profile105_node43_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 17 6 5 14 22), lower := (rows 17 6 5 14 16), losses := [] }

theorem profile105_node43 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,1,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,1,6] 2 profile105_node43_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,1,6] 2 profile105_node43_cert).mp (by decide +kernel))

def profile105_node42_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node42 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,1] 2 (by decide) (choices 2) [6] profile105_node42_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,1] (choices 2) [6] profile105_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node43

def profile105_node46_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 17 6 6 13 22), lower := (rows 17 6 6 13 22), losses := [] }

theorem profile105_node46 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2,5,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2,5,6] 2 profile105_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2,5,6] 2 profile105_node46_cert).mp (by decide +kernel))

def profile105_node45_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node45 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2,5] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2,5] 2 (by decide) (choices 2) [6] profile105_node45_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2,5] (choices 2) [6] profile105_node45_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node46

def profile105_node47_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 17 6 6 14 21), lower := (rows 17 6 6 14 16), losses := [] }

theorem profile105_node47 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2,6] 2 :=
  bound_sound (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2,6] 2 profile105_node47_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2,6] 2 profile105_node47_cert).mp (by decide +kernel))

def profile105_node44_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node44 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2] 2 (by decide) (choices 2) [5,6] profile105_node44_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4,2] (choices 2) [5,6] profile105_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile105_node45
  · exact profile105_node47

def profile105_node41_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node41 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4] 2 (by decide) (choices 1) [1,2] profile105_node41_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16,4] (choices 1) [1,2] profile105_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile105_node42
  · exact profile105_node44

def profile105_node40_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node40 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16] 2 (by decide) (choices 1) [4] profile105_node40_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [16] (choices 1) [4] profile105_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node41

def profile105_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node0 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [] 2 := by
  apply routed_branch (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [] 2 (by decide) (choices 1) [2,4,16] profile105_node0_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [] (choices 1) [2,4,16] profile105_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile105_node1
  · exact profile105_node13
  · exact profile105_node40

theorem profile105 : Upper (D (n:=5) [9,10,11,16,17]) (R (n:=5) [9,10,11,16,17]) [] 2 := profile105_node0

def profile106_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 5 6 5 14 22), lower := (rows 5 6 5 14 16), losses := [] }

theorem profile106_node4 : Upper (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,1,6] 2 :=
  bound_sound (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,1,6] 2 profile106_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,1,6] 2 profile106_node4_cert).mp (by decide +kernel))

def profile106_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile106_node3 : Upper (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,1] 2 := by
  apply routed_branch (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,1] 2 (by decide) (choices 2) [6] profile106_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,1] (choices 2) [6] profile106_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile106_node4

def profile106_node6_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 5 6 6 13 22), lower := (rows 5 6 6 13 16), losses := [{ target := 1, region := (rows 15 0 4 15 16), good := (rows 13 13 13 13 16) }] }

theorem profile106_node6 : Upper (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,2,5] 2 :=
  bound_sound (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,2,5] 2 profile106_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,2,5] 2 profile106_node6_cert).mp (by decide +kernel))

def profile106_node7_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 5 6 6 14 21), lower := (rows 5 6 6 14 16), losses := [] }

theorem profile106_node7 : Upper (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,2,6] 2 :=
  bound_sound (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,2,6] 2 profile106_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,2,6] 2 profile106_node7_cert).mp (by decide +kernel))

def profile106_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile106_node5 : Upper (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,2] 2 := by
  apply routed_branch (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,2] 2 (by decide) (choices 2) [5,6] profile106_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4,2] (choices 2) [5,6] profile106_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile106_node6
  · exact profile106_node7

def profile106_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile106_node2 : Upper (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4] 2 := by
  apply routed_branch (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4] 2 (by decide) (choices 1) [1,2] profile106_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4,4] (choices 1) [1,2] profile106_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile106_node3
  · exact profile106_node5

def profile106_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile106_node1 : Upper (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4] 2 := by
  apply routed_branch (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4] 2 (by decide) (choices 1) [4] profile106_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [4] (choices 1) [4] profile106_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile106_node2

def profile106_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile106_node0 : Upper (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [] 2 := by
  apply routed_branch (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [] 2 (by decide) (choices 1) [4] profile106_node0_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [] (choices 1) [4] profile106_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile106_node1

theorem profile106 : Upper (D (n:=5) [9,10,12,16,16]) (R (n:=5) [9,10,12,16,16]) [] 2 := profile106_node0

def profile107_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 3 6 5 14 22), lower := (rows 3 6 5 14 16), losses := [] }

theorem profile107_node4 : Upper (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,1,6] 2 :=
  bound_sound (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,1,6] 2 profile107_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,1,6] 2 profile107_node4_cert).mp (by decide +kernel))

def profile107_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile107_node3 : Upper (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,1] 2 := by
  apply routed_branch (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,1] 2 (by decide) (choices 2) [6] profile107_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,1] (choices 2) [6] profile107_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile107_node4

def profile107_node7_cert : Bound 5 := { allowed := (rows 0 0 0 2 0), upper := (rows 3 6 6 13 22), lower := (rows 3 6 6 13 22), losses := [] }

theorem profile107_node7 : Upper (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2,5,6] 2 :=
  bound_sound (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2,5,6] 2 profile107_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2,5,6] 2 profile107_node7_cert).mp (by decide +kernel))

def profile107_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile107_node6 : Upper (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2,5] 2 := by
  apply routed_branch (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2,5] 2 (by decide) (choices 2) [6] profile107_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2,5] (choices 2) [6] profile107_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile107_node7

def profile107_node8_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 3 6 6 14 21), lower := (rows 3 6 6 14 16), losses := [] }

theorem profile107_node8 : Upper (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2,6] 2 :=
  bound_sound (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2,6] 2 profile107_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2,6] 2 profile107_node8_cert).mp (by decide +kernel))

def profile107_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile107_node5 : Upper (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2] 2 := by
  apply routed_branch (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2] 2 (by decide) (choices 2) [5,6] profile107_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4,2] (choices 2) [5,6] profile107_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile107_node6
  · exact profile107_node8

def profile107_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile107_node2 : Upper (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4] 2 := by
  apply routed_branch (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4] 2 (by decide) (choices 1) [1,2] profile107_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2,4] (choices 1) [1,2] profile107_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile107_node3
  · exact profile107_node5

def profile107_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile107_node1 : Upper (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2] 2 := by
  apply routed_branch (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2] 2 (by decide) (choices 1) [4] profile107_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [2] (choices 1) [4] profile107_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile107_node2

def profile107_node0_route : Route 5 := (fun mask => match mask with | 4 => (2,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile107_node0 : Upper (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [] 2 := by
  apply routed_branch (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [] 2 (by decide) (choices 1) [2] profile107_node0_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [] (choices 1) [2] profile107_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile107_node1

theorem profile107 : Upper (D (n:=5) [9,11,11,16,16]) (R (n:=5) [9,11,11,16,16]) [] 2 := profile107_node0

def profile108_node5_cert : Bound 5 := { allowed := (rows 0 0 0 2 1), upper := (rows 3 3 5 28 22), lower := (rows 3 3 5 28 22), losses := [{ target := 0, region := (rows 0 2 4 24 16), good := (rows 2 2 4 28 30) }] }

theorem profile108_node5 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,1,20,6] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,1,20,6] 2 profile108_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,1,20,6] 2 profile108_node5_cert).mp (by decide +kernel))

def profile108_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node4 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,1,20] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,1,20] 2 (by decide) (choices 2) [6] profile108_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,1,20] (choices 2) [6] profile108_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node5

def profile108_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node3 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,1] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,1] 2 (by decide) (choices 2) [20] profile108_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,1] (choices 2) [20] profile108_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node4

def profile108_node8_cert : Bound 5 := { allowed := (rows 0 0 0 2 2), upper := (rows 3 3 6 28 21), lower := (rows 3 3 6 28 21), losses := [{ target := 0, region := (rows 0 2 7 24 16), good := (rows 6 6 6 28 28) }] }

theorem profile108_node8 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,2,20,5] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,2,20,5] 2 profile108_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,2,20,5] 2 profile108_node8_cert).mp (by decide +kernel))

def profile108_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node7 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,2,20] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,2,20] 2 (by decide) (choices 2) [5] profile108_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,2,20] (choices 2) [5] profile108_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node8

def profile108_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node6 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,2] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,2] 2 (by decide) (choices 2) [20] profile108_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,2] (choices 2) [20] profile108_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node7

def profile108_node11_cert : Bound 5 := { allowed := (rows 0 0 0 2 1), upper := (rows 3 3 20 13 22), lower := (rows 3 3 20 13 22), losses := [] }

theorem profile108_node11 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,5,6] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,5,6] 2 profile108_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,5,6] 2 profile108_node11_cert).mp (by decide +kernel))

def profile108_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node10 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,5] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,5] 2 (by decide) (choices 2) [6] profile108_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,5] (choices 2) [6] profile108_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node11

def profile108_node13_cert : Bound 5 := { allowed := (rows 0 0 0 1 2), upper := (rows 3 3 20 14 21), lower := (rows 3 3 20 14 21), losses := [] }

theorem profile108_node13 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,6,5] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,6,5] 2 profile108_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,6,5] 2 profile108_node13_cert).mp (by decide +kernel))

def profile108_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node12 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,6] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,6] 2 (by decide) (choices 2) [5] profile108_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16,6] (choices 2) [5] profile108_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node13

def profile108_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node9 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16] 2 (by decide) (choices 2) [5,6] profile108_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1,16] (choices 2) [5,6] profile108_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node10
  · exact profile108_node12

def profile108_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node2 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1] 2 (by decide) (choices 1) [1,2,16] profile108_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,1] (choices 1) [1,2,16] profile108_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile108_node3
  · exact profile108_node6
  · exact profile108_node9

def profile108_node17_cert : Bound 5 := { allowed := (rows 0 0 0 6 0), upper := (rows 3 6 5 25 22), lower := (rows 3 6 5 25 22), losses := [{ target := 0, region := (rows 0 22 4 8 22), good := (rows 18 22 22 26 22) }] }

theorem profile108_node17 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,17,6] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,17,6] 2 profile108_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,17,6] 2 profile108_node17_cert).mp (by decide +kernel))

def profile108_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node16 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,17] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,17] 2 (by decide) (choices 2) [6] profile108_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,17] (choices 2) [6] profile108_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node17

def profile108_node19_cert : Bound 5 := { allowed := (rows 0 0 0 4 2), upper := (rows 3 6 5 26 21), lower := (rows 3 6 5 26 21), losses := [{ target := 0, region := (rows 0 22 4 24 16), good := (rows 2 6 6 26 30) }] }

theorem profile108_node19 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,18,5] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,18,5] 2 profile108_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,18,5] 2 profile108_node19_cert).mp (by decide +kernel))

def profile108_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node18 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,18] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,18] 2 (by decide) (choices 2) [5] profile108_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,18] (choices 2) [5] profile108_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node19

def profile108_node21_cert : Bound 5 := { allowed := (rows 0 0 0 1 4), upper := (rows 3 6 5 28 19), lower := (rows 3 6 5 28 19), losses := [{ target := 1, region := (rows 1 0 21 24 16), good := (rows 5 4 5 28 29) }] }

theorem profile108_node21 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,20,3] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,20,3] 2 profile108_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,20,3] 2 profile108_node21_cert).mp (by decide +kernel))

def profile108_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node20 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,20] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,20] 2 (by decide) (choices 2) [3] profile108_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1,20] (choices 2) [3] profile108_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node21

def profile108_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node15 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1] 2 (by decide) (choices 2) [17,18,20] profile108_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,1] (choices 2) [17,18,20] profile108_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile108_node16
  · exact profile108_node18
  · exact profile108_node20

def profile108_node24_cert : Bound 5 := { allowed := (rows 0 0 0 4 2), upper := (rows 3 6 6 25 21), lower := (rows 3 6 6 25 21), losses := [{ target := 1, region := (rows 1 0 4 24 16), good := (rows 1 4 4 25 29) }] }

theorem profile108_node24 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,2,17,5] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,2,17,5] 2 profile108_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,2,17,5] 2 profile108_node24_cert).mp (by decide +kernel))

def profile108_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node23 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,2,17] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,2,17] 2 (by decide) (choices 2) [5] profile108_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,2,17] (choices 2) [5] profile108_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node24

def profile108_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node22 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,2] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,2] 2 (by decide) (choices 2) [17] profile108_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,2] (choices 2) [17] profile108_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node23

def profile108_node26_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 3 6 20 11 21), lower := (rows 3 6 20 11 16), losses := [{ target := 1, region := (rows 1 0 29 8 25), good := (rows 21 4 20 29 20) },{ target := 2, region := (rows 11 2 0 11 16), good := (rows 11 11 16 11 16) }] }

theorem profile108_node26 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16,3] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16,3] 2 profile108_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16,3] 2 profile108_node26_cert).mp (by decide +kernel))

def profile108_node28_cert : Bound 5 := { allowed := (rows 0 0 0 2 4), upper := (rows 3 6 20 13 19), lower := (rows 3 6 20 13 19), losses := [] }

theorem profile108_node28 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16,5,3] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16,5,3] 2 profile108_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16,5,3] 2 profile108_node28_cert).mp (by decide +kernel))

def profile108_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node27 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16,5] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16,5] 2 (by decide) (choices 2) [3] profile108_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16,5] (choices 2) [3] profile108_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node28

def profile108_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node25 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16] 2 (by decide) (choices 2) [3,5] profile108_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4,16] (choices 2) [3,5] profile108_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node26
  · exact profile108_node27

def profile108_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node14 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4] 2 (by decide) (choices 1) [1,2,16] profile108_node14_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,4] (choices 1) [1,2,16] profile108_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile108_node15
  · exact profile108_node22
  · exact profile108_node25

def profile108_node31_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 3 18 5 13 22), lower := (rows 3 18 5 13 16), losses := [{ target := 0, region := (rows 0 30 4 8 28), good := (rows 2 18 22 30 18) },{ target := 1, region := (rows 1 0 13 13 16), good := (rows 13 16 13 13 16) }] }

theorem profile108_node31 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1,5] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1,5] 2 profile108_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1,5] 2 profile108_node31_cert).mp (by decide +kernel))

def profile108_node33_cert : Bound 5 := { allowed := (rows 0 0 0 1 2), upper := (rows 3 18 5 14 21), lower := (rows 3 18 5 14 21), losses := [] }

theorem profile108_node33 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1,6,5] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1,6,5] 2 profile108_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1,6,5] 2 profile108_node33_cert).mp (by decide +kernel))

def profile108_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node32 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1,6] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1,6] 2 (by decide) (choices 2) [5] profile108_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1,6] (choices 2) [5] profile108_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node33

def profile108_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node30 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1] 2 (by decide) (choices 2) [5,6] profile108_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,1] (choices 2) [5,6] profile108_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node31
  · exact profile108_node32

def profile108_node36_cert : Bound 5 := { allowed := (rows 0 0 0 2 2), upper := (rows 3 18 6 13 21), lower := (rows 3 18 6 13 21), losses := [] }

theorem profile108_node36 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,2,5,5] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,2,5,5] 2 profile108_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,2,5,5] 2 profile108_node36_cert).mp (by decide +kernel))

def profile108_node35_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node35 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,2,5] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,2,5] 2 (by decide) (choices 2) [5] profile108_node35_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,2,5] (choices 2) [5] profile108_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node36

def profile108_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node34 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,2] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,2] 2 (by decide) (choices 2) [5] profile108_node34_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16,2] (choices 2) [5] profile108_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node35

def profile108_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node29 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16] 2 (by decide) (choices 1) [1,2] profile108_node29_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2,16] (choices 1) [1,2] profile108_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node30
  · exact profile108_node34

def profile108_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node1 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2] 2 (by decide) (choices 1) [1,4,16] profile108_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [2] (choices 1) [1,4,16] profile108_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile108_node2
  · exact profile108_node14
  · exact profile108_node29

def profile108_node41_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 17 3 5 14 22), lower := (rows 17 3 5 14 22), losses := [] }

theorem profile108_node41 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,1,6,6] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,1,6,6] 2 profile108_node41_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,1,6,6] 2 profile108_node41_cert).mp (by decide +kernel))

def profile108_node40_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node40 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,1,6] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,1,6] 2 (by decide) (choices 2) [6] profile108_node40_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,1,6] (choices 2) [6] profile108_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node41

def profile108_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node39 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,1] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,1] 2 (by decide) (choices 2) [6] profile108_node39_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,1] (choices 2) [6] profile108_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node40

def profile108_node44_cert : Bound 5 := { allowed := (rows 0 0 0 2 1), upper := (rows 17 3 6 13 22), lower := (rows 17 3 6 13 22), losses := [] }

theorem profile108_node44 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2,5,6] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2,5,6] 2 profile108_node44_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2,5,6] 2 profile108_node44_cert).mp (by decide +kernel))

def profile108_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node43 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2,5] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2,5] 2 (by decide) (choices 2) [6] profile108_node43_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2,5] (choices 2) [6] profile108_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node44

def profile108_node45_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 17 3 6 14 21), lower := (rows 17 3 6 14 16), losses := [{ target := 0, region := (rows 0 2 14 14 16), good := (rows 16 14 14 14 16) },{ target := 1, region := (rows 29 0 4 8 28), good := (rows 17 1 21 29 17) }] }

theorem profile108_node45 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2,6] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2,6] 2 profile108_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2,6] 2 profile108_node45_cert).mp (by decide +kernel))

def profile108_node42_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node42 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2] 2 (by decide) (choices 2) [5,6] profile108_node42_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1,2] (choices 2) [5,6] profile108_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node43
  · exact profile108_node45

def profile108_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node38 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1] 2 (by decide) (choices 1) [1,2] profile108_node38_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,1] (choices 1) [1,2] profile108_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node39
  · exact profile108_node42

def profile108_node49_cert : Bound 5 := { allowed := (rows 0 0 0 4 1), upper := (rows 17 6 5 11 22), lower := (rows 17 6 5 11 22), losses := [] }

theorem profile108_node49 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1,3,6] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1,3,6] 2 profile108_node49_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1,3,6] 2 profile108_node49_cert).mp (by decide +kernel))

def profile108_node48_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node48 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1,3] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1,3] 2 (by decide) (choices 2) [6] profile108_node48_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1,3] (choices 2) [6] profile108_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node49

def profile108_node50_cert : Bound 5 := { allowed := (rows 0 0 0 0 3), upper := (rows 17 6 5 14 19), lower := (rows 17 6 5 14 16), losses := [{ target := 0, region := (rows 0 14 4 14 16), good := (rows 16 14 14 14 16) },{ target := 2, region := (rows 27 2 0 8 26), good := (rows 17 19 1 27 17) }] }

theorem profile108_node50 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1,6] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1,6] 2 profile108_node50_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1,6] 2 profile108_node50_cert).mp (by decide +kernel))

def profile108_node47_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node47 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1] 2 (by decide) (choices 2) [3,6] profile108_node47_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,1] (choices 2) [3,6] profile108_node47_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node48
  · exact profile108_node50

def profile108_node53_cert : Bound 5 := { allowed := (rows 0 0 0 4 2), upper := (rows 17 6 6 11 21), lower := (rows 17 6 6 11 21), losses := [] }

theorem profile108_node53 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,3,5] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,3,5] 2 profile108_node53_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,3,5] 2 profile108_node53_cert).mp (by decide +kernel))

def profile108_node52_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node52 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,3] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,3] 2 (by decide) (choices 2) [5] profile108_node52_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,3] (choices 2) [5] profile108_node52_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node53

def profile108_node55_cert : Bound 5 := { allowed := (rows 0 0 0 2 4), upper := (rows 17 6 6 13 19), lower := (rows 17 6 6 13 19), losses := [] }

theorem profile108_node55 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,5,3] 2 :=
  bound_sound (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,5,3] 2 profile108_node55_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,5,3] 2 profile108_node55_cert).mp (by decide +kernel))

def profile108_node54_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node54 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,5] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,5] 2 (by decide) (choices 2) [3] profile108_node54_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2,5] (choices 2) [3] profile108_node54_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node55

def profile108_node51_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node51 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2] 2 (by decide) (choices 2) [3,5] profile108_node51_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4,2] (choices 2) [3,5] profile108_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node52
  · exact profile108_node54

def profile108_node46_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node46 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4] 2 (by decide) (choices 1) [1,2] profile108_node46_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16,4] (choices 1) [1,2] profile108_node46_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node47
  · exact profile108_node51

def profile108_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node37 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16] 2 (by decide) (choices 1) [1,4] profile108_node37_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [16] (choices 1) [1,4] profile108_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node38
  · exact profile108_node46

def profile108_node0_route : Route 5 := (fun mask => match mask with | 4 => (2,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile108_node0 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [] 2 := by
  apply routed_branch (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [] 2 (by decide) (choices 1) [2,16] profile108_node0_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [] (choices 1) [2,16] profile108_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node1
  · exact profile108_node37

theorem profile108 : Upper (D (n:=5) [10,10,10,16,17]) (R (n:=5) [10,10,10,16,17]) [] 2 := profile108_node0

def profile109_node4_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 3 6 5 13 22), lower := (rows 3 6 5 13 16), losses := [{ target := 0, region := (rows 0 14 4 8 30), good := (rows 18 22 22 30 16) },{ target := 1, region := (rows 1 0 13 13 16), good := (rows 13 12 13 13 16) }] }

theorem profile109_node4 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,1,5] 2 :=
  bound_sound (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,1,5] 2 profile109_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,1,5] 2 profile109_node4_cert).mp (by decide +kernel))

def profile109_node5_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 3 6 5 14 21), lower := (rows 3 6 5 14 16), losses := [{ target := 0, region := (rows 0 14 4 14 16), good := (rows 10 14 14 14 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 21 20 21 28 16) }] }

theorem profile109_node5 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,1,6] 2 :=
  bound_sound (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,1,6] 2 profile109_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,1,6] 2 profile109_node5_cert).mp (by decide +kernel))

def profile109_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node3 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,1] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,1] 2 (by decide) (choices 2) [5,6] profile109_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,1] (choices 2) [5,6] profile109_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile109_node4
  · exact profile109_node5

def profile109_node8_cert : Bound 5 := { allowed := (rows 0 0 0 2 2), upper := (rows 3 6 6 13 21), lower := (rows 3 6 6 13 21), losses := [] }

theorem profile109_node8 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,2,5,5] 2 :=
  bound_sound (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,2,5,5] 2 profile109_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,2,5,5] 2 profile109_node8_cert).mp (by decide +kernel))

def profile109_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node7 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,2,5] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,2,5] 2 (by decide) (choices 2) [5] profile109_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,2,5] (choices 2) [5] profile109_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile109_node8

def profile109_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node6 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,2] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,2] 2 (by decide) (choices 2) [5] profile109_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4,2] (choices 2) [5] profile109_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile109_node7

def profile109_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node2 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4] 2 (by decide) (choices 1) [1,2] profile109_node2_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2,4] (choices 1) [1,2] profile109_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile109_node3
  · exact profile109_node6

def profile109_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node1 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2] 2 (by decide) (choices 1) [4] profile109_node1_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [2] (choices 1) [4] profile109_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile109_node2

def profile109_node13_cert : Bound 5 := { allowed := (rows 0 0 0 1 1), upper := (rows 5 3 5 14 22), lower := (rows 5 3 5 14 22), losses := [] }

theorem profile109_node13 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,1,6,6] 2 :=
  bound_sound (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,1,6,6] 2 profile109_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,1,6,6] 2 profile109_node13_cert).mp (by decide +kernel))

def profile109_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node12 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,1,6] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,1,6] 2 (by decide) (choices 2) [6] profile109_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,1,6] (choices 2) [6] profile109_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile109_node13

def profile109_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node11 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,1] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,1] 2 (by decide) (choices 2) [6] profile109_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,1] (choices 2) [6] profile109_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile109_node12

def profile109_node15_cert : Bound 5 := { allowed := (rows 0 0 0 0 6), upper := (rows 5 3 6 13 22), lower := (rows 5 3 6 13 16), losses := [{ target := 0, region := (rows 0 2 6 8 22), good := (rows 20 22 22 28 16) },{ target := 1, region := (rows 13 0 4 13 16), good := (rows 13 9 13 13 16) }] }

theorem profile109_node15 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,2,5] 2 :=
  bound_sound (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,2,5] 2 profile109_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,2,5] 2 profile109_node15_cert).mp (by decide +kernel))

def profile109_node16_cert : Bound 5 := { allowed := (rows 0 0 0 0 5), upper := (rows 5 3 6 14 21), lower := (rows 5 3 6 14 16), losses := [{ target := 0, region := (rows 0 2 14 14 16), good := (rows 12 14 14 14 16) },{ target := 1, region := (rows 13 0 4 8 29), good := (rows 21 17 21 29 16) }] }

theorem profile109_node16 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,2,6] 2 :=
  bound_sound (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,2,6] 2 profile109_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,2,6] 2 profile109_node16_cert).mp (by decide +kernel))

def profile109_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node14 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,2] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,2] 2 (by decide) (choices 2) [5,6] profile109_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1,2] (choices 2) [5,6] profile109_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile109_node15
  · exact profile109_node16

def profile109_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node10 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1] 2 (by decide) (choices 1) [1,2] profile109_node10_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,1] (choices 1) [1,2] profile109_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile109_node11
  · exact profile109_node14

def profile109_node20_cert : Bound 5 := { allowed := (rows 0 0 0 4 1), upper := (rows 5 6 5 11 22), lower := (rows 5 6 5 11 22), losses := [] }

theorem profile109_node20 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,3,6] 2 :=
  bound_sound (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,3,6] 2 profile109_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,3,6] 2 profile109_node20_cert).mp (by decide +kernel))

def profile109_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node19 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,3] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,3] 2 (by decide) (choices 2) [6] profile109_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,3] (choices 2) [6] profile109_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile109_node20

def profile109_node22_cert : Bound 5 := { allowed := (rows 0 0 0 1 4), upper := (rows 5 6 5 14 19), lower := (rows 5 6 5 14 19), losses := [] }

theorem profile109_node22 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,6,3] 2 :=
  bound_sound (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,6,3] 2 profile109_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,6,3] 2 profile109_node22_cert).mp (by decide +kernel))

def profile109_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node21 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,6] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,6] 2 (by decide) (choices 2) [3] profile109_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1,6] (choices 2) [3] profile109_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile109_node22

def profile109_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node18 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1] 2 (by decide) (choices 2) [3,6] profile109_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,1] (choices 2) [3,6] profile109_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile109_node19
  · exact profile109_node21

def profile109_node25_cert : Bound 5 := { allowed := (rows 0 0 0 4 2), upper := (rows 5 6 6 11 21), lower := (rows 5 6 6 11 21), losses := [] }

theorem profile109_node25 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,3,5] 2 :=
  bound_sound (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,3,5] 2 profile109_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,3,5] 2 profile109_node25_cert).mp (by decide +kernel))

def profile109_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node24 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,3] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,3] 2 (by decide) (choices 2) [5] profile109_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,3] (choices 2) [5] profile109_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile109_node25

def profile109_node27_cert : Bound 5 := { allowed := (rows 0 0 0 2 4), upper := (rows 5 6 6 13 19), lower := (rows 5 6 6 13 19), losses := [] }

theorem profile109_node27 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,5,3] 2 :=
  bound_sound (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,5,3] 2 profile109_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,5,3] 2 profile109_node27_cert).mp (by decide +kernel))

def profile109_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node26 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,5] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,5] 2 (by decide) (choices 2) [3] profile109_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2,5] (choices 2) [3] profile109_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile109_node27

def profile109_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node23 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2] 2 (by decide) (choices 2) [3,5] profile109_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4,2] (choices 2) [3,5] profile109_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile109_node24
  · exact profile109_node26

def profile109_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node17 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4] 2 (by decide) (choices 1) [1,2] profile109_node17_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4,4] (choices 1) [1,2] profile109_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile109_node18
  · exact profile109_node23

def profile109_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node9 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4] 2 (by decide) (choices 1) [1,4] profile109_node9_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [4] (choices 1) [1,4] profile109_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile109_node10
  · exact profile109_node17

def profile109_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node0 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [] 2 := by
  apply routed_branch (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [] 2 (by decide) (choices 1) [2,4] profile109_node0_route
    (by change RowCover 5 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [] (choices 1) [2,4] profile109_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile109_node1
  · exact profile109_node9

theorem profile109 : Upper (D (n:=5) [10,10,11,16,16]) (R (n:=5) [10,10,11,16,16]) [] 2 := profile109_node0

def catalogue : List (List Nat) := [[2,2,2,24,33],[2,2,2,25,32],[2,2,3,24,32],[2,2,9,16,34],[2,2,9,17,33],[2,2,9,18,32],[2,2,9,24,26],[2,2,9,25,25],[2,2,10,16,33],[2,2,10,17,32],[2,2,10,24,25],[2,2,11,16,32],[2,2,11,24,24],[2,2,16,16,27],[2,2,16,17,26],[2,2,16,18,25],[2,2,16,19,24],[2,2,17,17,25],[2,2,17,18,24],[2,3,9,16,33],[2,3,9,17,32],[2,3,9,24,25],[2,3,10,16,32],[2,3,10,24,24],[2,3,16,16,26],[2,3,16,17,25],[2,3,16,18,24],[2,3,17,17,24],[2,4,9,16,32],[2,4,9,24,24],[2,4,16,16,25],[2,4,16,17,24],[2,9,9,9,34],[2,9,9,10,33],[2,9,9,11,32],[2,9,9,16,27],[2,9,9,17,26],[2,9,9,18,25],[2,9,9,19,24],[2,9,10,10,32],[2,9,10,16,26],[2,9,10,17,25],[2,9,10,18,24],[2,9,11,16,25],[2,9,11,17,24],[2,9,12,16,24],[2,9,16,16,20],[2,9,16,17,19],[2,9,16,18,18],[2,9,17,17,18],[2,10,10,16,25],[2,10,10,17,24],[2,10,11,16,24],[2,10,16,16,19],[2,10,16,17,18],[2,10,17,17,17],[2,11,16,16,18],[2,11,16,17,17],[2,12,16,16,17],[3,3,9,16,32],[3,3,9,24,24],[3,3,16,16,25],[3,3,16,17,24],[3,4,16,16,24],[3,9,9,9,33],[3,9,9,10,32],[3,9,9,16,26],[3,9,9,17,25],[3,9,9,18,24],[3,9,10,16,25],[3,9,10,17,24],[3,9,11,16,24],[3,9,16,16,19],[3,9,16,17,18],[3,9,17,17,17],[3,10,10,16,24],[3,10,16,16,18],[3,10,16,17,17],[3,11,16,16,17],[3,12,16,16,16],[4,9,9,9,32],[4,9,9,16,25],[4,9,9,17,24],[4,9,10,16,24],[4,9,16,16,18],[4,9,16,17,17],[4,10,16,16,17],[4,11,16,16,16],[9,9,9,9,27],[9,9,9,10,26],[9,9,9,11,25],[9,9,9,12,24],[9,9,9,16,20],[9,9,9,17,19],[9,9,9,18,18],[9,9,10,10,25],[9,9,10,11,24],[9,9,10,16,19],[9,9,10,17,18],[9,9,11,16,18],[9,9,11,17,17],[9,9,12,16,17],[9,10,10,10,24],[9,10,10,16,18],[9,10,10,17,17],[9,10,11,16,17],[9,10,12,16,16],[9,11,11,16,16],[10,10,10,16,17],[10,10,11,16,16]]

theorem catalogue_eq : profiles 5 5 0 7 7=catalogue := by decide +kernel

theorem profile_upper (xs : List Nat) (member : xs∈profiles 5 5 0 7 7) :
    Upper (n:=5) (D xs) (R xs) [] 2 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact profile52
  · exact profile53
  · exact profile54
  · exact profile55
  · exact profile56
  · exact profile57
  · exact profile58
  · exact profile59
  · exact profile60
  · exact profile61
  · exact profile62
  · exact profile63
  · exact profile64
  · exact profile65
  · exact profile66
  · exact profile67
  · exact profile68
  · exact profile69
  · exact profile70
  · exact profile71
  · exact profile72
  · exact profile73
  · exact profile74
  · exact profile75
  · exact profile76
  · exact profile77
  · exact profile78
  · exact profile79
  · exact profile80
  · exact profile81
  · exact profile82
  · exact profile83
  · exact profile84
  · exact profile85
  · exact profile86
  · exact profile87
  · exact profile88
  · exact profile89
  · exact profile90
  · exact profile91
  · exact profile92
  · exact profile93
  · exact profile94
  · exact profile95
  · exact profile96
  · exact profile97
  · exact profile98
  · exact profile99
  · exact profile100
  · exact profile101
  · exact profile102
  · exact profile103
  · exact profile104
  · exact profile105
  · exact profile106
  · exact profile107
  · exact profile108
  · exact profile109
theorem upper (E : Graph (Fin 5)) (loops : Loopless E) (budget : arcCount E=7)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x) : score E≤2 := by
  have od (x) : SparseSupport.outdegree E x<5 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<5 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 5).map (SparseSupport.outdegree E)).sum=7 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 5).map (SparseSupport.indegree E)).sum=7 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    (by decide) od idg degree td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetSevenOrder5
