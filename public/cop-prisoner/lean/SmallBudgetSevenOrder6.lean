import SmallRowPrefixBoolean
import SmallDegreeProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
6 vertices with seven arrows and total degree at least two at each vertex. -/
namespace Delivery.SmallBudgetSevenOrder6
open FiniteGame Extremal RowPrefix SmallDegreeProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e f : Nat) : Rows 6 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16,32]
  | 2 => [3,5,9,17,33,6,10,18,34,12,20,36,24,40,48]
  | 3 => [7,11,19,35,13,21,37,25,41,49,14,22,38,26,42,50,28,44,52,56]
  | 4 => [15,23,39,27,43,51,29,45,53,57,30,46,54,58,60]
  | 5 => [31,47,55,59,61,62]
  | 6 => [63]
  | _ => []

theorem cover (d : Fin 7) : RowCover 6 d.val (choices d.val) := by
  revert d
  decide +kernel

def profile0_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 2 4 9 22 47), lower := (rows 1 2 4 9 22 47), losses := [] }

theorem profile0_node6 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,1,6,15] 2 :=
  bound_sound (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,1,6,15] 2 profile0_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,1,6,15] 2 profile0_node6_cert).mp (by decide +kernel))

def profile0_node5_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node5 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,1,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,1,6] 2 (by decide) (choices 4) [15] profile0_node5_route
    (by change RowCover 6 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,1,6] (choices 4) [15] profile0_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node6

def profile0_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node4 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,1] 2 (by decide) (choices 2) [6] profile0_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,1] (choices 2) [6] profile0_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node5

def profile0_node9_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 0), upper := (rows 1 2 4 10 21 47), lower := (rows 1 2 4 10 21 47), losses := [] }

theorem profile0_node9 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,2,5,15] 2 :=
  bound_sound (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,2,5,15] 2 profile0_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,2,5,15] 2 profile0_node9_cert).mp (by decide +kernel))

def profile0_node8_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node8 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,2,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,2,5] 2 (by decide) (choices 4) [15] profile0_node8_route
    (by change RowCover 6 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,2,5] (choices 4) [15] profile0_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node9

def profile0_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node7 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,2] 2 (by decide) (choices 2) [5] profile0_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,2] (choices 2) [5] profile0_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node8

def profile0_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 4 0), upper := (rows 1 2 4 12 19 47), lower := (rows 1 2 4 12 19 47), losses := [] }

theorem profile0_node12 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,4,3,15] 2 :=
  bound_sound (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,4,3,15] 2 profile0_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,4,3,15] 2 profile0_node12_cert).mp (by decide +kernel))

def profile0_node11_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node11 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,4,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,4,3] 2 (by decide) (choices 4) [15] profile0_node11_route
    (by change RowCover 6 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,4,3] (choices 4) [15] profile0_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node12

def profile0_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node10 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,4] 2 (by decide) (choices 2) [3] profile0_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0,4] (choices 2) [3] profile0_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node11

def profile0_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node3 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0] 2 (by decide) (choices 1) [1,2,4] profile0_node3_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0,0] (choices 1) [1,2,4] profile0_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node4
  · exact profile0_node7
  · exact profile0_node10

def profile0_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node2 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0] 2 (by decide) (choices 0) [0] profile0_node2_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0,0] (choices 0) [0] profile0_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node3

def profile0_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node1 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0] 2 (by decide) (choices 0) [0] profile0_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [0] (choices 0) [0] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node2

def profile0_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node0 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [] 2 (by decide) (choices 0) [0] profile0_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [] (choices 0) [0] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=6) [2,2,2,9,16,32]) (R (n:=6) [2,2,2,9,16,32]) [] 2 := profile0_node0

def profile1_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 4 9 23 46), lower := (rows 1 2 4 9 23 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 40), good := (rows 6 6 6 46 22 38) }] }

theorem profile1_node5 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1,7] 2 profile1_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1,7] 2 profile1_node5_cert).mp (by decide +kernel))

def profile1_node7_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 2 4 9 30 39), lower := (rows 1 2 4 9 30 39), losses := [] }

theorem profile1_node7 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1,14,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1,14,7] 2 profile1_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1,14,7] 2 profile1_node7_cert).mp (by decide +kernel))

def profile1_node6_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node6 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1,14] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1,14] 2 (by decide) (choices 3) [7] profile1_node6_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1,14] (choices 3) [7] profile1_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node7

def profile1_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node4 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1] 2 (by decide) (choices 3) [7,14] profile1_node4_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,1] (choices 3) [7,14] profile1_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node5
  · exact profile1_node6

def profile1_node9_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 4 10 23 45), lower := (rows 1 2 4 10 23 32), losses := [{ target := 1, region := (rows 63 0 63 8 16 40), good := (rows 5 5 5 45 21 37) }] }

theorem profile1_node9 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2,7] 2 profile1_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2,7] 2 profile1_node9_cert).mp (by decide +kernel))

def profile1_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 0), upper := (rows 1 2 4 10 29 39), lower := (rows 1 2 4 10 29 39), losses := [] }

theorem profile1_node11 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2,13,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2,13,7] 2 profile1_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2,13,7] 2 profile1_node11_cert).mp (by decide +kernel))

def profile1_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node10 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2,13] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2,13] 2 (by decide) (choices 3) [7] profile1_node10_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2,13] (choices 3) [7] profile1_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node11

def profile1_node8_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node8 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2] 2 (by decide) (choices 3) [7,13] profile1_node8_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,2] (choices 3) [7,13] profile1_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node9
  · exact profile1_node10

def profile1_node13_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 4 12 23 43), lower := (rows 1 2 4 12 23 32), losses := [{ target := 2, region := (rows 63 63 0 8 16 40), good := (rows 3 3 3 43 19 35) }] }

theorem profile1_node13 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4,7] 2 profile1_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4,7] 2 profile1_node13_cert).mp (by decide +kernel))

def profile1_node15_cert : Bound 6 := { allowed := (rows 0 0 0 0 4 0), upper := (rows 1 2 4 12 27 39), lower := (rows 1 2 4 12 27 39), losses := [] }

theorem profile1_node15 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4,11,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4,11,7] 2 profile1_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4,11,7] 2 profile1_node15_cert).mp (by decide +kernel))

def profile1_node14_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node14 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4,11] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4,11] 2 (by decide) (choices 3) [7] profile1_node14_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4,11] (choices 3) [7] profile1_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node15

def profile1_node12_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node12 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4] 2 (by decide) (choices 3) [7,11] profile1_node12_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0,4] (choices 3) [7,11] profile1_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node13
  · exact profile1_node14

def profile1_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node3 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0] 2 (by decide) (choices 1) [1,2,4] profile1_node3_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0,0] (choices 1) [1,2,4] profile1_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node4
  · exact profile1_node8
  · exact profile1_node12

def profile1_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node2 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0] 2 (by decide) (choices 0) [0] profile1_node2_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0,0] (choices 0) [0] profile1_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node3

def profile1_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node1 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0] 2 (by decide) (choices 0) [0] profile1_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [0] (choices 0) [0] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node2

def profile1_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node0 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [] 2 (by decide) (choices 0) [0] profile1_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [] (choices 0) [0] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node1

theorem profile1 : Upper (D (n:=6) [2,2,2,9,24,24]) (R (n:=6) [2,2,2,9,24,24]) [] 2 := profile1_node0

def profile2_node6_cert : Bound 6 := { allowed := (rows 0 0 0 4 2 0), upper := (rows 1 2 4 11 52 39), lower := (rows 1 2 4 11 52 39), losses := [{ target := 0, region := (rows 0 63 63 8 48 32), good := (rows 6 6 6 14 54 54) }] }

theorem profile2_node6 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,3,36,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,3,36,7] 2 profile2_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,3,36,7] 2 profile2_node6_cert).mp (by decide +kernel))

def profile2_node5_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node5 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,3,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,3,36] 2 (by decide) (choices 3) [7] profile2_node5_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,3,36] (choices 3) [7] profile2_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node6

def profile2_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node4 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,3] 2 (by decide) (choices 2) [36] profile2_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,3] (choices 2) [36] profile2_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node5

def profile2_node9_cert : Bound 6 := { allowed := (rows 0 0 0 2 4 0), upper := (rows 1 2 4 13 50 39), lower := (rows 1 2 4 13 50 39), losses := [{ target := 0, region := (rows 0 63 63 8 48 32), good := (rows 6 6 6 14 54 54) }] }

theorem profile2_node9 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,5,34,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,5,34,7] 2 profile2_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,5,34,7] 2 profile2_node9_cert).mp (by decide +kernel))

def profile2_node8_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node8 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,5,34] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,5,34] 2 (by decide) (choices 3) [7] profile2_node8_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,5,34] (choices 3) [7] profile2_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node9

def profile2_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node7 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,5] 2 (by decide) (choices 2) [34] profile2_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,5] (choices 2) [34] profile2_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node8

def profile2_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 6 0), upper := (rows 1 2 4 14 49 39), lower := (rows 1 2 4 14 49 39), losses := [{ target := 0, region := (rows 0 63 63 63 16 32), good := (rows 14 14 14 14 62 46) }] }

theorem profile2_node12 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,6,33,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,6,33,7] 2 profile2_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,6,33,7] 2 profile2_node12_cert).mp (by decide +kernel))

def profile2_node11_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node11 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,6,33] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,6,33] 2 (by decide) (choices 3) [7] profile2_node11_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,6,33] (choices 3) [7] profile2_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node12

def profile2_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node10 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,6] 2 (by decide) (choices 2) [33] profile2_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,6] (choices 2) [33] profile2_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node11

def profile2_node15_cert : Bound 6 := { allowed := (rows 0 0 0 6 0 0), upper := (rows 1 2 4 41 22 39), lower := (rows 1 2 4 41 22 39), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 62 22 54) }] }

theorem profile2_node15 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,33,6,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,33,6,7] 2 profile2_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,33,6,7] 2 profile2_node15_cert).mp (by decide +kernel))

def profile2_node14_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node14 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,33,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,33,6] 2 (by decide) (choices 3) [7] profile2_node14_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,33,6] (choices 3) [7] profile2_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node15

def profile2_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node13 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,33] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,33] 2 (by decide) (choices 2) [6] profile2_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,33] (choices 2) [6] profile2_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node14

def profile2_node18_cert : Bound 6 := { allowed := (rows 0 0 0 4 2 0), upper := (rows 1 2 4 42 21 39), lower := (rows 1 2 4 42 21 39), losses := [{ target := 0, region := (rows 0 63 63 40 16 32), good := (rows 6 6 6 46 22 46) }] }

theorem profile2_node18 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,34,5,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,34,5,7] 2 profile2_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,34,5,7] 2 profile2_node18_cert).mp (by decide +kernel))

def profile2_node17_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node17 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,34,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,34,5] 2 (by decide) (choices 3) [7] profile2_node17_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,34,5] (choices 3) [7] profile2_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node18

def profile2_node16_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node16 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,34] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,34] 2 (by decide) (choices 2) [5] profile2_node16_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,34] (choices 2) [5] profile2_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node17

def profile2_node21_cert : Bound 6 := { allowed := (rows 0 0 0 2 4 0), upper := (rows 1 2 4 44 19 39), lower := (rows 1 2 4 44 19 39), losses := [{ target := 0, region := (rows 0 63 63 40 16 32), good := (rows 6 6 6 46 22 46) }] }

theorem profile2_node21 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,36,3,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,36,3,7] 2 profile2_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,36,3,7] 2 profile2_node21_cert).mp (by decide +kernel))

def profile2_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node20 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,36,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,36,3] 2 (by decide) (choices 3) [7] profile2_node20_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,36,3] (choices 3) [7] profile2_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node21

def profile2_node19_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node19 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,36] 2 (by decide) (choices 2) [3] profile2_node19_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0,36] (choices 2) [3] profile2_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node20

def profile2_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node3 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0] 2 (by decide) (choices 2) [3,5,6,33,34,36] profile2_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0,0] (choices 2) [3,5,6,33,34,36] profile2_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node4
  · exact profile2_node7
  · exact profile2_node10
  · exact profile2_node13
  · exact profile2_node16
  · exact profile2_node19

def profile2_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node2 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0] 2 (by decide) (choices 0) [0] profile2_node2_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0,0] (choices 0) [0] profile2_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node3

def profile2_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node1 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0] 2 (by decide) (choices 0) [0] profile2_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [0] (choices 0) [0] profile2_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node2

def profile2_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node0 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [] 2 (by decide) (choices 0) [0] profile2_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [] (choices 0) [0] profile2_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node1

theorem profile2 : Upper (D (n:=6) [2,2,2,16,16,25]) (R (n:=6) [2,2,2,16,16,25]) [] 2 := profile2_node0

def profile3_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 4 11 21 54), lower := (rows 1 2 4 11 21 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 48), good := (rows 6 6 6 14 54 38) },{ target := 1, region := (rows 63 0 63 8 63 32), good := (rows 21 21 21 29 21 53) },{ target := 2, region := (rows 63 63 0 63 16 32), good := (rows 11 11 11 11 27 43) }] }

theorem profile3_node5 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,3,5] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,3,5] 2 profile3_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,3,5] 2 profile3_node5_cert).mp (by decide +kernel))

def profile3_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 4 11 22 53), lower := (rows 1 2 4 11 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 30 22 54) },{ target := 1, region := (rows 63 0 63 8 16 48), good := (rows 5 5 5 13 53 37) },{ target := 2, region := (rows 63 63 0 63 16 32), good := (rows 11 11 11 11 27 43) }] }

theorem profile3_node6 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,3,6] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,3,6] 2 profile3_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,3,6] 2 profile3_node6_cert).mp (by decide +kernel))

def profile3_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node4 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,3] 2 (by decide) (choices 2) [5,6] profile3_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,3] (choices 2) [5,6] profile3_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node5
  · exact profile3_node6

def profile3_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 4 13 19 54), lower := (rows 1 2 4 13 19 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 48), good := (rows 6 6 6 14 54 38) },{ target := 1, region := (rows 63 0 63 63 16 32), good := (rows 13 13 13 13 29 45) },{ target := 2, region := (rows 63 63 0 8 63 32), good := (rows 19 19 19 27 19 51) }] }

theorem profile3_node8 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,5,3] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,5,3] 2 profile3_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,5,3] 2 profile3_node8_cert).mp (by decide +kernel))

def profile3_node9_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 4 13 22 51), lower := (rows 1 2 4 13 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 30 22 54) },{ target := 1, region := (rows 63 0 63 63 16 32), good := (rows 13 13 13 13 29 45) },{ target := 2, region := (rows 63 63 0 8 16 48), good := (rows 3 3 3 11 51 35) }] }

theorem profile3_node9 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,5,6] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,5,6] 2 profile3_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,5,6] 2 profile3_node9_cert).mp (by decide +kernel))

def profile3_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node7 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,5] 2 (by decide) (choices 2) [3,6] profile3_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,5] (choices 2) [3,6] profile3_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node8
  · exact profile3_node9

def profile3_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 4 14 19 53), lower := (rows 1 2 4 14 19 32), losses := [{ target := 0, region := (rows 0 63 63 63 16 32), good := (rows 14 14 14 14 30 46) },{ target := 1, region := (rows 63 0 63 8 16 48), good := (rows 5 5 5 13 53 37) },{ target := 2, region := (rows 63 63 0 8 63 32), good := (rows 19 19 19 27 19 51) }] }

theorem profile3_node11 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,6,3] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,6,3] 2 profile3_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,6,3] 2 profile3_node11_cert).mp (by decide +kernel))

def profile3_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 4 14 21 51), lower := (rows 1 2 4 14 21 32), losses := [{ target := 0, region := (rows 0 63 63 63 16 32), good := (rows 14 14 14 14 30 46) },{ target := 1, region := (rows 63 0 63 8 63 32), good := (rows 21 21 21 29 21 53) },{ target := 2, region := (rows 63 63 0 8 16 48), good := (rows 3 3 3 11 51 35) }] }

theorem profile3_node12 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,6,5] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,6,5] 2 profile3_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,6,5] 2 profile3_node12_cert).mp (by decide +kernel))

def profile3_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node10 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,6] 2 (by decide) (choices 2) [3,5] profile3_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,6] (choices 2) [3,5] profile3_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node11
  · exact profile3_node12

def profile3_node15_cert : Bound 6 := { allowed := (rows 0 0 0 6 0 0), upper := (rows 1 2 4 25 22 39), lower := (rows 1 2 4 25 22 39), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 30 22 54) }] }

theorem profile3_node15 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,17,6,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,17,6,7] 2 profile3_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,17,6,7] 2 profile3_node15_cert).mp (by decide +kernel))

def profile3_node14_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node14 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,17,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,17,6] 2 (by decide) (choices 3) [7] profile3_node14_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,17,6] (choices 3) [7] profile3_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node15

def profile3_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node13 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,17] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,17] 2 (by decide) (choices 2) [6] profile3_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,17] (choices 2) [6] profile3_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node14

def profile3_node18_cert : Bound 6 := { allowed := (rows 0 0 0 4 2 0), upper := (rows 1 2 4 26 21 39), lower := (rows 1 2 4 26 21 39), losses := [{ target := 0, region := (rows 0 63 63 24 16 32), good := (rows 6 6 6 30 30 38) }] }

theorem profile3_node18 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,18,5,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,18,5,7] 2 profile3_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,18,5,7] 2 profile3_node18_cert).mp (by decide +kernel))

def profile3_node17_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node17 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,18,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,18,5] 2 (by decide) (choices 3) [7] profile3_node17_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,18,5] (choices 3) [7] profile3_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node18

def profile3_node16_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node16 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,18] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,18] 2 (by decide) (choices 2) [5] profile3_node16_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,18] (choices 2) [5] profile3_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node17

def profile3_node21_cert : Bound 6 := { allowed := (rows 0 0 0 2 4 0), upper := (rows 1 2 4 28 19 39), lower := (rows 1 2 4 28 19 39), losses := [{ target := 0, region := (rows 0 63 63 24 16 32), good := (rows 6 6 6 30 30 38) }] }

theorem profile3_node21 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,20,3,7] 2 :=
  bound_sound (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,20,3,7] 2 profile3_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,20,3,7] 2 profile3_node21_cert).mp (by decide +kernel))

def profile3_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node20 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,20,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,20,3] 2 (by decide) (choices 3) [7] profile3_node20_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,20,3] (choices 3) [7] profile3_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node21

def profile3_node19_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node19 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,20] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,20] 2 (by decide) (choices 2) [3] profile3_node19_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0,20] (choices 2) [3] profile3_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node20

def profile3_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node3 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0] 2 (by decide) (choices 2) [3,5,6,17,18,20] profile3_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0,0] (choices 2) [3,5,6,17,18,20] profile3_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node4
  · exact profile3_node7
  · exact profile3_node10
  · exact profile3_node13
  · exact profile3_node16
  · exact profile3_node19

def profile3_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node2 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0] 2 (by decide) (choices 0) [0] profile3_node2_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0,0] (choices 0) [0] profile3_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node3

def profile3_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node1 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0] 2 (by decide) (choices 0) [0] profile3_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [0] (choices 0) [0] profile3_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node2

def profile3_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node0 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [] 2 (by decide) (choices 0) [0] profile3_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [] (choices 0) [0] profile3_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node1

theorem profile3 : Upper (D (n:=6) [2,2,2,16,17,24]) (R (n:=6) [2,2,2,16,17,24]) [] 2 := profile3_node0

def profile4_node6_cert : Bound 6 := { allowed := (rows 0 0 0 2 1 0), upper := (rows 1 2 4 13 22 39), lower := (rows 1 2 4 13 22 39), losses := [] }

theorem profile4_node6 : Upper (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,5,6,7] 2 :=
  bound_sound (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,5,6,7] 2 profile4_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,5,6,7] 2 profile4_node6_cert).mp (by decide +kernel))

def profile4_node5_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node5 : Upper (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,5,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,5,6] 2 (by decide) (choices 3) [7] profile4_node5_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,5,6] (choices 3) [7] profile4_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node6

def profile4_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node4 : Upper (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,5] 2 (by decide) (choices 2) [6] profile4_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,5] (choices 2) [6] profile4_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node5

def profile4_node9_cert : Bound 6 := { allowed := (rows 0 0 0 1 2 0), upper := (rows 1 2 4 14 21 39), lower := (rows 1 2 4 14 21 39), losses := [] }

theorem profile4_node9 : Upper (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,6,5,7] 2 :=
  bound_sound (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,6,5,7] 2 profile4_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,6,5,7] 2 profile4_node9_cert).mp (by decide +kernel))

def profile4_node8_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node8 : Upper (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,6,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,6,5] 2 (by decide) (choices 3) [7] profile4_node8_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,6,5] (choices 3) [7] profile4_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node9

def profile4_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node7 : Upper (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,6] 2 (by decide) (choices 2) [5] profile4_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0,6] (choices 2) [5] profile4_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node8

def profile4_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node3 : Upper (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0] 2 (by decide) (choices 2) [5,6] profile4_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0,0] (choices 2) [5,6] profile4_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node4
  · exact profile4_node7

def profile4_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node2 : Upper (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0] 2 (by decide) (choices 0) [0] profile4_node2_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0,0] (choices 0) [0] profile4_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node3

def profile4_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node1 : Upper (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0] 2 (by decide) (choices 0) [0] profile4_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [0] (choices 0) [0] profile4_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node2

def profile4_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node0 : Upper (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [] 2 (by decide) (choices 0) [0] profile4_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [] (choices 0) [0] profile4_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node1

theorem profile4 : Upper (D (n:=6) [2,2,3,16,16,24]) (R (n:=6) [2,2,3,16,16,24]) [] 2 := profile4_node0

def profile5_node0_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 31 31 31 31 31 63), lower := (rows 1 2 4 8 16 32), losses := [] }

theorem profile5_node0 : Upper (D (n:=6) [2,2,9,9,9,32]) (R (n:=6) [2,2,9,9,9,32]) [] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,9,32]) (R (n:=6) [2,2,9,9,9,32]) [] 2 profile5_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,9,32]) (R (n:=6) [2,2,9,9,9,32]) [] 2 profile5_node0_cert).mp (by decide +kernel))

theorem profile5 : Upper (D (n:=6) [2,2,9,9,9,32]) (R (n:=6) [2,2,9,9,9,32]) [] 2 := profile5_node0

def profile6_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 9 50 46), lower := (rows 1 2 5 9 50 32), losses := [{ target := 0, region := (rows 0 63 4 8 48 32), good := (rows 2 2 6 10 50 50) }] }

theorem profile6_node5 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,1,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,1,34] 2 profile6_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,1,34] 2 profile6_node5_cert).mp (by decide +kernel))

def profile6_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node4 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,1] 2 (by decide) (choices 2) [34] profile6_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,1] (choices 2) [34] profile6_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node5

def profile6_node7_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 5 10 49 46), lower := (rows 1 2 5 10 49 32), losses := [{ target := 0, region := (rows 0 63 4 63 16 36), good := (rows 10 10 46 10 58 42) }] }

theorem profile6_node7 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,33] 2 profile6_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,33] 2 profile6_node7_cert).mp (by decide +kernel))

def profile6_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 10 50 45), lower := (rows 1 2 5 10 50 32), losses := [{ target := 0, region := (rows 0 63 4 63 48 32), good := (rows 10 10 14 10 58 58) }] }

theorem profile6_node8 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,34] 2 profile6_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,34] 2 profile6_node8_cert).mp (by decide +kernel))

def profile6_node10_cert : Bound 6 := { allowed := (rows 0 0 0 0 3 0), upper := (rows 1 2 5 10 52 43), lower := (rows 1 2 5 10 52 43), losses := [] }

theorem profile6_node10 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,36,11] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,36,11] 2 profile6_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,36,11] 2 profile6_node10_cert).mp (by decide +kernel))

def profile6_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node9 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,36] 2 (by decide) (choices 3) [11] profile6_node9_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,36] (choices 3) [11] profile6_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node10

def profile6_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 3 0), upper := (rows 1 2 5 10 56 39), lower := (rows 1 2 5 10 56 39), losses := [] }

theorem profile6_node12 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,40,7] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,40,7] 2 profile6_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,40,7] 2 profile6_node12_cert).mp (by decide +kernel))

def profile6_node11_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node11 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,40] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,40] 2 (by decide) (choices 3) [7] profile6_node11_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2,40] (choices 3) [7] profile6_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node12

def profile6_node6_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node6 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2] 2 (by decide) (choices 2) [33,34,36,40] profile6_node6_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,2] (choices 2) [33,34,36,40] profile6_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node7
  · exact profile6_node8
  · exact profile6_node9
  · exact profile6_node11

def profile6_node14_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 12 50 43), lower := (rows 1 2 5 12 50 32), losses := [{ target := 0, region := (rows 0 63 4 12 48 32), good := (rows 2 2 14 14 50 50) }] }

theorem profile6_node14 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,4,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,4,34] 2 profile6_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,4,34] 2 profile6_node14_cert).mp (by decide +kernel))

def profile6_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node13 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,4] 2 (by decide) (choices 2) [34] profile6_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,4] (choices 2) [34] profile6_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node14

def profile6_node16_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 40 19 46), lower := (rows 1 2 5 40 19 32), losses := [] }

theorem profile6_node16 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32,3] 2 profile6_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32,3] 2 profile6_node16_cert).mp (by decide +kernel))

def profile6_node17_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 40 22 43), lower := (rows 1 2 5 40 22 32), losses := [{ target := 0, region := (rows 0 63 4 40 20 32), good := (rows 2 2 22 42 22 42) }] }

theorem profile6_node17 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32,6] 2 profile6_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32,6] 2 profile6_node17_cert).mp (by decide +kernel))

def profile6_node18_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 40 26 39), lower := (rows 1 2 5 40 26 32), losses := [{ target := 0, region := (rows 0 63 4 40 56 32), good := (rows 2 2 6 58 26 58) }] }

theorem profile6_node18 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32,10] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32,10] 2 profile6_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32,10] 2 profile6_node18_cert).mp (by decide +kernel))

def profile6_node15_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node15 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32] 2 (by decide) (choices 2) [3,6,10] profile6_node15_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1,32] (choices 2) [3,6,10] profile6_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node16
  · exact profile6_node17
  · exact profile6_node18

def profile6_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node3 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1] 2 (by decide) (choices 1) [1,2,4,32] profile6_node3_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,1] (choices 1) [1,2,4,32] profile6_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node4
  · exact profile6_node6
  · exact profile6_node13
  · exact profile6_node15

def profile6_node21_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 6 9 49 46), lower := (rows 1 2 6 9 49 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 40), good := (rows 6 6 6 46 54 38) }] }

theorem profile6_node21 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,33] 2 profile6_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,33] 2 profile6_node21_cert).mp (by decide +kernel))

def profile6_node22_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 9 50 45), lower := (rows 1 2 6 9 50 32), losses := [{ target := 0, region := (rows 0 63 63 8 48 32), good := (rows 6 6 6 14 54 54) }] }

theorem profile6_node22 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,34] 2 profile6_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,34] 2 profile6_node22_cert).mp (by decide +kernel))

def profile6_node24_cert : Bound 6 := { allowed := (rows 0 0 0 0 3 0), upper := (rows 1 2 6 9 52 43), lower := (rows 1 2 6 9 52 43), losses := [] }

theorem profile6_node24 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,36,11] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,36,11] 2 profile6_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,36,11] 2 profile6_node24_cert).mp (by decide +kernel))

def profile6_node23_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node23 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,36] 2 (by decide) (choices 3) [11] profile6_node23_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,36] (choices 3) [11] profile6_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node24

def profile6_node26_cert : Bound 6 := { allowed := (rows 0 0 0 0 3 0), upper := (rows 1 2 6 9 56 39), lower := (rows 1 2 6 9 56 39), losses := [] }

theorem profile6_node26 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,40,7] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,40,7] 2 profile6_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,40,7] 2 profile6_node26_cert).mp (by decide +kernel))

def profile6_node25_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node25 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,40] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,40] 2 (by decide) (choices 3) [7] profile6_node25_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1,40] (choices 3) [7] profile6_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node26

def profile6_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node20 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1] 2 (by decide) (choices 2) [33,34,36,40] profile6_node20_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,1] (choices 2) [33,34,36,40] profile6_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node21
  · exact profile6_node22
  · exact profile6_node23
  · exact profile6_node25

def profile6_node28_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 10 49 45), lower := (rows 1 2 6 10 49 32), losses := [{ target := 1, region := (rows 63 0 4 8 48 32), good := (rows 1 1 5 9 49 49) }] }

theorem profile6_node28 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,2,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,2,33] 2 profile6_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,2,33] 2 profile6_node28_cert).mp (by decide +kernel))

def profile6_node27_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node27 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,2] 2 (by decide) (choices 2) [33] profile6_node27_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,2] (choices 2) [33] profile6_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node28

def profile6_node30_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 12 49 43), lower := (rows 1 2 6 12 49 32), losses := [{ target := 1, region := (rows 63 0 4 12 48 32), good := (rows 1 1 13 13 49 49) }] }

theorem profile6_node30 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,4,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,4,33] 2 profile6_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,4,33] 2 profile6_node30_cert).mp (by decide +kernel))

def profile6_node29_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node29 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,4] 2 (by decide) (choices 2) [33] profile6_node29_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,4] (choices 2) [33] profile6_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node30

def profile6_node32_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 40 19 45), lower := (rows 1 2 6 40 19 32), losses := [] }

theorem profile6_node32 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32,3] 2 profile6_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32,3] 2 profile6_node32_cert).mp (by decide +kernel))

def profile6_node33_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 40 21 43), lower := (rows 1 2 6 40 21 32), losses := [{ target := 1, region := (rows 63 0 4 40 20 32), good := (rows 1 1 21 41 21 41) }] }

theorem profile6_node33 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32,5] 2 profile6_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32,5] 2 profile6_node33_cert).mp (by decide +kernel))

def profile6_node34_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 40 25 39), lower := (rows 1 2 6 40 25 32), losses := [{ target := 1, region := (rows 63 0 4 40 56 32), good := (rows 1 1 5 57 25 57) }] }

theorem profile6_node34 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32,9] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32,9] 2 profile6_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32,9] 2 profile6_node34_cert).mp (by decide +kernel))

def profile6_node31_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node31 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32] 2 (by decide) (choices 2) [3,5,9] profile6_node31_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2,32] (choices 2) [3,5,9] profile6_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node32
  · exact profile6_node33
  · exact profile6_node34

def profile6_node19_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node19 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2] 2 (by decide) (choices 1) [1,2,4,32] profile6_node19_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,2] (choices 1) [1,2,4,32] profile6_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node20
  · exact profile6_node27
  · exact profile6_node29
  · exact profile6_node31

def profile6_node37_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 9 50 39), lower := (rows 1 2 12 9 50 32), losses := [{ target := 0, region := (rows 0 63 12 8 48 32), good := (rows 2 2 14 14 50 50) }] }

theorem profile6_node37 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,1,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,1,34] 2 profile6_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,1,34] 2 profile6_node37_cert).mp (by decide +kernel))

def profile6_node36_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node36 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,1] 2 (by decide) (choices 2) [34] profile6_node36_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,1] (choices 2) [34] profile6_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node37

def profile6_node39_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 10 49 39), lower := (rows 1 2 12 10 49 32), losses := [{ target := 1, region := (rows 63 0 12 8 48 32), good := (rows 1 1 13 13 49 49) }] }

theorem profile6_node39 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,2,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,2,33] 2 profile6_node39_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,2,33] 2 profile6_node39_cert).mp (by decide +kernel))

def profile6_node38_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node38 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,2] 2 (by decide) (choices 2) [33] profile6_node38_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,2] (choices 2) [33] profile6_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node39

def profile6_node40_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node40 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,4] 2 (by decide) (choices 2) [] profile6_node40_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,4] (choices 2) [] profile6_node40_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile6_node42_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 40 19 39), lower := (rows 1 2 12 40 19 32), losses := [] }

theorem profile6_node42 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,32,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,32,3] 2 profile6_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,32,3] 2 profile6_node42_cert).mp (by decide +kernel))

def profile6_node41_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node41 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,32] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,32] 2 (by decide) (choices 2) [3] profile6_node41_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8,32] (choices 2) [3] profile6_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node42

def profile6_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node35 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8] 2 (by decide) (choices 1) [1,2,4,32] profile6_node35_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,8] (choices 1) [1,2,4,32] profile6_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node36
  · exact profile6_node38
  · exact profile6_node40
  · exact profile6_node41

def profile6_node45_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 9 19 46), lower := (rows 1 2 36 9 19 32), losses := [] }

theorem profile6_node45 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1,3] 2 profile6_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1,3] 2 profile6_node45_cert).mp (by decide +kernel))

def profile6_node46_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 9 22 43), lower := (rows 1 2 36 9 22 32), losses := [{ target := 0, region := (rows 0 63 36 8 52 32), good := (rows 2 2 54 10 22 54) }] }

theorem profile6_node46 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1,6] 2 profile6_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1,6] 2 profile6_node46_cert).mp (by decide +kernel))

def profile6_node47_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 9 26 39), lower := (rows 1 2 36 9 26 32), losses := [{ target := 0, region := (rows 0 63 36 8 24 32), good := (rows 2 2 38 26 26 38) }] }

theorem profile6_node47 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1,10] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1,10] 2 profile6_node47_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1,10] 2 profile6_node47_cert).mp (by decide +kernel))

def profile6_node44_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node44 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1] 2 (by decide) (choices 2) [3,6,10] profile6_node44_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,1] (choices 2) [3,6,10] profile6_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node45
  · exact profile6_node46
  · exact profile6_node47

def profile6_node49_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 10 19 45), lower := (rows 1 2 36 10 19 32), losses := [] }

theorem profile6_node49 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2,3] 2 profile6_node49_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2,3] 2 profile6_node49_cert).mp (by decide +kernel))

def profile6_node50_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 10 21 43), lower := (rows 1 2 36 10 21 32), losses := [{ target := 1, region := (rows 63 0 36 8 52 32), good := (rows 1 1 53 9 21 53) }] }

theorem profile6_node50 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2,5] 2 profile6_node50_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2,5] 2 profile6_node50_cert).mp (by decide +kernel))

def profile6_node51_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 10 25 39), lower := (rows 1 2 36 10 25 32), losses := [{ target := 1, region := (rows 63 0 36 8 24 32), good := (rows 1 1 37 25 25 37) }] }

theorem profile6_node51 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2,9] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2,9] 2 profile6_node51_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2,9] 2 profile6_node51_cert).mp (by decide +kernel))

def profile6_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node48 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2] 2 (by decide) (choices 2) [3,5,9] profile6_node48_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,2] (choices 2) [3,5,9] profile6_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node49
  · exact profile6_node50
  · exact profile6_node51

def profile6_node53_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 12 19 43), lower := (rows 1 2 36 12 19 32), losses := [] }

theorem profile6_node53 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,4,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,4,3] 2 profile6_node53_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,4,3] 2 profile6_node53_cert).mp (by decide +kernel))

def profile6_node52_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node52 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,4] 2 (by decide) (choices 2) [3] profile6_node52_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32,4] (choices 2) [3] profile6_node52_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node53

def profile6_node43_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node43 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32] 2 (by decide) (choices 1) [1,2,4] profile6_node43_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0,32] (choices 1) [1,2,4] profile6_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node44
  · exact profile6_node48
  · exact profile6_node52

def profile6_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node2 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0] 2 (by decide) (choices 1) [1,2,8,32] profile6_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0,0] (choices 1) [1,2,8,32] profile6_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node3
  · exact profile6_node19
  · exact profile6_node35
  · exact profile6_node43

def profile6_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node1 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0] 2 (by decide) (choices 0) [0] profile6_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [0] (choices 0) [0] profile6_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node2

def profile6_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile6_node0 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [] 2 (by decide) (choices 0) [0] profile6_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [] (choices 0) [0] profile6_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node1

theorem profile6 : Upper (D (n:=6) [2,2,9,9,16,25]) (R (n:=6) [2,2,9,9,16,25]) [] 2 := profile6_node0

def profile7_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 9 22 58), lower := (rows 1 2 5 9 22 32), losses := [{ target := 0, region := (rows 0 63 4 8 20 32), good := (rows 2 2 22 10 22 34) }] }

theorem profile7_node5 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,1,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,1,6] 2 profile7_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,1,6] 2 profile7_node5_cert).mp (by decide +kernel))

def profile7_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 9 26 54), lower := (rows 1 2 5 9 26 32), losses := [{ target := 0, region := (rows 0 63 4 8 24 32), good := (rows 2 2 6 26 26 34) }] }

theorem profile7_node6 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,1,10] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,1,10] 2 profile7_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,1,10] 2 profile7_node6_cert).mp (by decide +kernel))

def profile7_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node4 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,1] 2 (by decide) (choices 2) [6,10] profile7_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,1] (choices 2) [6,10] profile7_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile7_node5
  · exact profile7_node6

def profile7_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 10 19 60), lower := (rows 1 2 5 10 19 32), losses := [] }

theorem profile7_node8 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,3] 2 profile7_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,3] 2 profile7_node8_cert).mp (by decide +kernel))

def profile7_node9_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 5 10 21 58), lower := (rows 1 2 5 10 21 32), losses := [{ target := 0, region := (rows 0 63 4 63 16 48), good := (rows 10 10 14 10 62 42) }] }

theorem profile7_node9 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,5] 2 profile7_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,5] 2 profile7_node9_cert).mp (by decide +kernel))

def profile7_node10_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 10 22 57), lower := (rows 1 2 5 10 22 32), losses := [{ target := 0, region := (rows 0 63 4 63 20 32), good := (rows 10 10 30 10 30 42) }] }

theorem profile7_node10 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,6] 2 profile7_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,6] 2 profile7_node10_cert).mp (by decide +kernel))

def profile7_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 10 25 54), lower := (rows 1 2 5 10 25 32), losses := [{ target := 1, region := (rows 63 0 63 8 24 32), good := (rows 5 5 5 29 29 37) }] }

theorem profile7_node11 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,9] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,9] 2 profile7_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,9] 2 profile7_node11_cert).mp (by decide +kernel))

def profile7_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 10 26 53), lower := (rows 1 2 5 10 26 32), losses := [{ target := 0, region := (rows 0 63 4 63 63 32), good := (rows 26 26 30 26 26 58) }] }

theorem profile7_node12 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,10] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,10] 2 profile7_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,10] 2 profile7_node12_cert).mp (by decide +kernel))

def profile7_node13_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 10 28 51), lower := (rows 1 2 5 10 28 32), losses := [{ target := 0, region := (rows 0 63 4 63 20 32), good := (rows 10 10 30 10 30 42) },{ target := 1, region := (rows 63 0 63 8 24 32), good := (rows 5 5 5 29 29 37) }] }

theorem profile7_node13 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,12] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,12] 2 profile7_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2,12] 2 profile7_node13_cert).mp (by decide +kernel))

def profile7_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node7 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile7_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,2] (choices 2) [3,5,6,9,10,12] profile7_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node8
  · exact profile7_node9
  · exact profile7_node10
  · exact profile7_node11
  · exact profile7_node12
  · exact profile7_node13

def profile7_node15_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 12 19 58), lower := (rows 1 2 5 12 19 32), losses := [] }

theorem profile7_node15 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,4,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,4,3] 2 profile7_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,4,3] 2 profile7_node15_cert).mp (by decide +kernel))

def profile7_node16_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 12 26 51), lower := (rows 1 2 5 12 26 32), losses := [{ target := 0, region := (rows 0 63 4 12 28 32), good := (rows 2 2 30 30 26 34) }] }

theorem profile7_node16 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,4,10] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,4,10] 2 profile7_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,4,10] 2 profile7_node16_cert).mp (by decide +kernel))

def profile7_node14_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node14 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,4] 2 (by decide) (choices 2) [3,10] profile7_node14_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,4] (choices 2) [3,10] profile7_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile7_node15
  · exact profile7_node16

def profile7_node18_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 24 19 46), lower := (rows 1 2 5 24 19 32), losses := [] }

theorem profile7_node18 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16,3] 2 profile7_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16,3] 2 profile7_node18_cert).mp (by decide +kernel))

def profile7_node19_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 24 22 43), lower := (rows 1 2 5 24 22 32), losses := [{ target := 0, region := (rows 0 63 4 28 20 32), good := (rows 2 2 30 26 30 34) }] }

theorem profile7_node19 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16,6] 2 profile7_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16,6] 2 profile7_node19_cert).mp (by decide +kernel))

def profile7_node20_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 24 26 39), lower := (rows 1 2 5 24 26 32), losses := [{ target := 0, region := (rows 0 63 4 63 63 32), good := (rows 26 26 30 26 26 58) }] }

theorem profile7_node20 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16,10] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16,10] 2 profile7_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16,10] 2 profile7_node20_cert).mp (by decide +kernel))

def profile7_node17_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node17 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16] 2 (by decide) (choices 2) [3,6,10] profile7_node17_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1,16] (choices 2) [3,6,10] profile7_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node18
  · exact profile7_node19
  · exact profile7_node20

def profile7_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node3 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1] 2 (by decide) (choices 1) [1,2,4,16] profile7_node3_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,1] (choices 1) [1,2,4,16] profile7_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node4
  · exact profile7_node7
  · exact profile7_node14
  · exact profile7_node17

def profile7_node23_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 9 19 60), lower := (rows 1 2 6 9 19 32), losses := [] }

theorem profile7_node23 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,3] 2 profile7_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,3] 2 profile7_node23_cert).mp (by decide +kernel))

def profile7_node24_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 9 21 58), lower := (rows 1 2 6 9 21 32), losses := [{ target := 1, region := (rows 63 0 4 63 20 32), good := (rows 9 9 29 9 29 41) }] }

theorem profile7_node24 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,5] 2 profile7_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,5] 2 profile7_node24_cert).mp (by decide +kernel))

def profile7_node25_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 9 22 57), lower := (rows 1 2 6 9 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 30 22 54) }] }

theorem profile7_node25 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,6] 2 profile7_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,6] 2 profile7_node25_cert).mp (by decide +kernel))

def profile7_node26_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 6 9 25 54), lower := (rows 1 2 6 9 25 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 48), good := (rows 6 6 6 14 62 38) }] }

theorem profile7_node26 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,9] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,9] 2 profile7_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,9] 2 profile7_node26_cert).mp (by decide +kernel))

def profile7_node27_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 9 26 53), lower := (rows 1 2 6 9 26 32), losses := [{ target := 0, region := (rows 0 63 63 8 24 32), good := (rows 6 6 6 30 30 38) }] }

theorem profile7_node27 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,10] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,10] 2 profile7_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,10] 2 profile7_node27_cert).mp (by decide +kernel))

def profile7_node28_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 9 28 51), lower := (rows 1 2 6 9 28 32), losses := [{ target := 0, region := (rows 0 63 63 8 24 32), good := (rows 6 6 6 30 30 38) },{ target := 1, region := (rows 63 0 4 63 20 32), good := (rows 9 9 29 9 29 41) }] }

theorem profile7_node28 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,12] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,12] 2 profile7_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1,12] 2 profile7_node28_cert).mp (by decide +kernel))

def profile7_node22_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node22 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile7_node22_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,1] (choices 2) [3,5,6,9,10,12] profile7_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node23
  · exact profile7_node24
  · exact profile7_node25
  · exact profile7_node26
  · exact profile7_node27
  · exact profile7_node28

def profile7_node30_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 10 21 57), lower := (rows 1 2 6 10 21 32), losses := [{ target := 1, region := (rows 63 0 4 8 20 32), good := (rows 1 1 21 9 21 33) }] }

theorem profile7_node30 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,2,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,2,5] 2 profile7_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,2,5] 2 profile7_node30_cert).mp (by decide +kernel))

def profile7_node31_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 10 25 53), lower := (rows 1 2 6 10 25 32), losses := [{ target := 1, region := (rows 63 0 4 8 24 32), good := (rows 1 1 5 25 25 33) }] }

theorem profile7_node31 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,2,9] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,2,9] 2 profile7_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,2,9] 2 profile7_node31_cert).mp (by decide +kernel))

def profile7_node29_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node29 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,2] 2 (by decide) (choices 2) [5,9] profile7_node29_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,2] (choices 2) [5,9] profile7_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile7_node30
  · exact profile7_node31

def profile7_node33_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 12 19 57), lower := (rows 1 2 6 12 19 32), losses := [] }

theorem profile7_node33 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,4,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,4,3] 2 profile7_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,4,3] 2 profile7_node33_cert).mp (by decide +kernel))

def profile7_node34_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 12 25 51), lower := (rows 1 2 6 12 25 32), losses := [{ target := 1, region := (rows 63 0 4 12 28 32), good := (rows 1 1 29 29 25 33) }] }

theorem profile7_node34 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,4,9] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,4,9] 2 profile7_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,4,9] 2 profile7_node34_cert).mp (by decide +kernel))

def profile7_node32_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node32 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,4] 2 (by decide) (choices 2) [3,9] profile7_node32_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,4] (choices 2) [3,9] profile7_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile7_node33
  · exact profile7_node34

def profile7_node36_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 24 19 45), lower := (rows 1 2 6 24 19 32), losses := [] }

theorem profile7_node36 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16,3] 2 profile7_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16,3] 2 profile7_node36_cert).mp (by decide +kernel))

def profile7_node37_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 24 21 43), lower := (rows 1 2 6 24 21 32), losses := [{ target := 1, region := (rows 63 0 4 28 20 32), good := (rows 1 1 29 25 29 33) }] }

theorem profile7_node37 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16,5] 2 profile7_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16,5] 2 profile7_node37_cert).mp (by decide +kernel))

def profile7_node38_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 24 25 39), lower := (rows 1 2 6 24 25 32), losses := [{ target := 1, region := (rows 63 0 4 63 63 32), good := (rows 25 25 29 25 25 57) }] }

theorem profile7_node38 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16,9] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16,9] 2 profile7_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16,9] 2 profile7_node38_cert).mp (by decide +kernel))

def profile7_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node35 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16] 2 (by decide) (choices 2) [3,5,9] profile7_node35_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2,16] (choices 2) [3,5,9] profile7_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node36
  · exact profile7_node37
  · exact profile7_node38

def profile7_node21_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node21 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2] 2 (by decide) (choices 1) [1,2,4,16] profile7_node21_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,2] (choices 1) [1,2,4,16] profile7_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node22
  · exact profile7_node29
  · exact profile7_node32
  · exact profile7_node35

def profile7_node41_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 9 19 54), lower := (rows 1 2 12 9 19 32), losses := [] }

theorem profile7_node41 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,1,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,1,3] 2 profile7_node41_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,1,3] 2 profile7_node41_cert).mp (by decide +kernel))

def profile7_node42_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 9 22 51), lower := (rows 1 2 12 9 22 32), losses := [{ target := 0, region := (rows 0 63 12 8 28 32), good := (rows 2 2 30 30 22 34) }] }

theorem profile7_node42 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,1,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,1,6] 2 profile7_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,1,6] 2 profile7_node42_cert).mp (by decide +kernel))

def profile7_node40_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node40 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,1] 2 (by decide) (choices 2) [3,6] profile7_node40_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,1] (choices 2) [3,6] profile7_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile7_node41
  · exact profile7_node42

def profile7_node44_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 10 19 53), lower := (rows 1 2 12 10 19 32), losses := [] }

theorem profile7_node44 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,2,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,2,3] 2 profile7_node44_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,2,3] 2 profile7_node44_cert).mp (by decide +kernel))

def profile7_node45_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 10 21 51), lower := (rows 1 2 12 10 21 32), losses := [{ target := 1, region := (rows 63 0 12 8 28 32), good := (rows 1 1 29 29 21 33) }] }

theorem profile7_node45 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,2,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,2,5] 2 profile7_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,2,5] 2 profile7_node45_cert).mp (by decide +kernel))

def profile7_node43_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node43 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,2] 2 (by decide) (choices 2) [3,5] profile7_node43_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,2] (choices 2) [3,5] profile7_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile7_node44
  · exact profile7_node45

def profile7_node47_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 12 19 51), lower := (rows 1 2 12 12 19 32), losses := [] }

theorem profile7_node47 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,4,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,4,3] 2 profile7_node47_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,4,3] 2 profile7_node47_cert).mp (by decide +kernel))

def profile7_node46_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node46 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,4] 2 (by decide) (choices 2) [3] profile7_node46_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,4] (choices 2) [3] profile7_node46_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node47

def profile7_node49_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 24 19 39), lower := (rows 1 2 12 24 19 32), losses := [] }

theorem profile7_node49 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,16,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,16,3] 2 profile7_node49_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,16,3] 2 profile7_node49_cert).mp (by decide +kernel))

def profile7_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node48 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,16] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,16] 2 (by decide) (choices 2) [3] profile7_node48_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8,16] (choices 2) [3] profile7_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node49

def profile7_node39_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node39 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8] 2 (by decide) (choices 1) [1,2,4,16] profile7_node39_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,8] (choices 1) [1,2,4,16] profile7_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node40
  · exact profile7_node43
  · exact profile7_node46
  · exact profile7_node48

def profile7_node52_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 9 19 46), lower := (rows 1 2 20 9 19 32), losses := [] }

theorem profile7_node52 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1,3] 2 profile7_node52_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1,3] 2 profile7_node52_cert).mp (by decide +kernel))

def profile7_node53_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 9 22 43), lower := (rows 1 2 20 9 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 30 22 54) }] }

theorem profile7_node53 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1,6] 2 profile7_node53_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1,6] 2 profile7_node53_cert).mp (by decide +kernel))

def profile7_node54_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 9 26 39), lower := (rows 1 2 20 9 26 32), losses := [{ target := 0, region := (rows 0 63 28 8 24 32), good := (rows 2 2 22 30 30 34) }] }

theorem profile7_node54 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1,10] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1,10] 2 profile7_node54_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1,10] 2 profile7_node54_cert).mp (by decide +kernel))

def profile7_node51_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node51 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1] 2 (by decide) (choices 2) [3,6,10] profile7_node51_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,1] (choices 2) [3,6,10] profile7_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node52
  · exact profile7_node53
  · exact profile7_node54

def profile7_node56_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 10 19 45), lower := (rows 1 2 20 10 19 32), losses := [] }

theorem profile7_node56 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2,3] 2 profile7_node56_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2,3] 2 profile7_node56_cert).mp (by decide +kernel))

def profile7_node57_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 10 21 43), lower := (rows 1 2 20 10 21 32), losses := [{ target := 1, region := (rows 63 0 63 8 63 32), good := (rows 21 21 21 29 21 53) }] }

theorem profile7_node57 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2,5] 2 profile7_node57_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2,5] 2 profile7_node57_cert).mp (by decide +kernel))

def profile7_node58_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 10 25 39), lower := (rows 1 2 20 10 25 32), losses := [{ target := 1, region := (rows 63 0 28 8 24 32), good := (rows 1 1 21 29 29 33) }] }

theorem profile7_node58 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2,9] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2,9] 2 profile7_node58_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2,9] 2 profile7_node58_cert).mp (by decide +kernel))

def profile7_node55_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node55 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2] 2 (by decide) (choices 2) [3,5,9] profile7_node55_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,2] (choices 2) [3,5,9] profile7_node55_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node56
  · exact profile7_node57
  · exact profile7_node58

def profile7_node60_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 12 19 43), lower := (rows 1 2 20 12 19 32), losses := [] }

theorem profile7_node60 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,4,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,4,3] 2 profile7_node60_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,4,3] 2 profile7_node60_cert).mp (by decide +kernel))

def profile7_node59_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node59 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,4] 2 (by decide) (choices 2) [3] profile7_node59_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16,4] (choices 2) [3] profile7_node59_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node60

def profile7_node50_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node50 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16] 2 (by decide) (choices 1) [1,2,4] profile7_node50_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0,16] (choices 1) [1,2,4] profile7_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node51
  · exact profile7_node55
  · exact profile7_node59

def profile7_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node2 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0] 2 (by decide) (choices 1) [1,2,8,16] profile7_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0,0] (choices 1) [1,2,8,16] profile7_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node3
  · exact profile7_node21
  · exact profile7_node39
  · exact profile7_node50

def profile7_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node1 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0] 2 (by decide) (choices 0) [0] profile7_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [0] (choices 0) [0] profile7_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node2

def profile7_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node0 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [] 2 (by decide) (choices 0) [0] profile7_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [] (choices 0) [0] profile7_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node1

theorem profile7 : Upper (D (n:=6) [2,2,9,9,17,24]) (R (n:=6) [2,2,9,9,17,24]) [] 2 := profile7_node0

def profile8_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 2 5 9 26 46), lower := (rows 1 2 5 9 26 46), losses := [] }

theorem profile8_node6 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,1,10,14] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,1,10,14] 2 profile8_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,1,10,14] 2 profile8_node6_cert).mp (by decide +kernel))

def profile8_node5_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node5 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,1,10] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,1,10] 2 (by decide) (choices 3) [14] profile8_node5_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,1,10] (choices 3) [14] profile8_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node6

def profile8_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node4 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,1] 2 (by decide) (choices 2) [10] profile8_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,1] (choices 2) [10] profile8_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node5

def profile8_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 10), upper := (rows 1 2 5 10 25 46), lower := (rows 1 2 5 10 25 32), losses := [{ target := 0, region := (rows 0 63 4 63 16 36), good := (rows 10 10 46 10 26 42) },{ target := 1, region := (rows 63 0 63 8 24 32), good := (rows 5 5 5 29 29 37) }] }

theorem profile8_node8 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,9] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,9] 2 profile8_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,9] 2 profile8_node8_cert).mp (by decide +kernel))

def profile8_node9_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 2 5 10 26 45), lower := (rows 1 2 5 10 26 32), losses := [{ target := 0, region := (rows 0 63 4 63 63 32), good := (rows 26 26 30 26 26 58) },{ target := 1, region := (rows 63 0 63 8 16 56), good := (rows 5 5 5 45 61 37) }] }

theorem profile8_node9 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,10] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,10] 2 profile8_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,10] 2 profile8_node9_cert).mp (by decide +kernel))

def profile8_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 3 0), upper := (rows 1 2 5 10 28 43), lower := (rows 1 2 5 10 28 43), losses := [] }

theorem profile8_node11 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,12,11] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,12,11] 2 profile8_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,12,11] 2 profile8_node11_cert).mp (by decide +kernel))

def profile8_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node10 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,12] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,12] 2 (by decide) (choices 3) [11] profile8_node10_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2,12] (choices 3) [11] profile8_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node11

def profile8_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node7 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2] 2 (by decide) (choices 2) [9,10,12] profile8_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,2] (choices 2) [9,10,12] profile8_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node8
  · exact profile8_node9
  · exact profile8_node10

def profile8_node14_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 2 5 12 26 43), lower := (rows 1 2 5 12 26 43), losses := [] }

theorem profile8_node14 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,4,10,11] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,4,10,11] 2 profile8_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,4,10,11] 2 profile8_node14_cert).mp (by decide +kernel))

def profile8_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node13 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,4,10] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,4,10] 2 (by decide) (choices 3) [11] profile8_node13_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,4,10] (choices 3) [11] profile8_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node14

def profile8_node12_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node12 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,4] 2 (by decide) (choices 2) [10] profile8_node12_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1,4] (choices 2) [10] profile8_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node13

def profile8_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node3 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1] 2 (by decide) (choices 1) [1,2,4] profile8_node3_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,1] (choices 1) [1,2,4] profile8_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node4
  · exact profile8_node7
  · exact profile8_node12

def profile8_node17_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 10), upper := (rows 1 2 6 9 25 46), lower := (rows 1 2 6 9 25 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 56), good := (rows 6 6 6 46 62 38) },{ target := 1, region := (rows 63 0 4 63 63 32), good := (rows 25 25 29 25 25 57) }] }

theorem profile8_node17 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,9] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,9] 2 profile8_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,9] 2 profile8_node17_cert).mp (by decide +kernel))

def profile8_node18_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 2 6 9 26 45), lower := (rows 1 2 6 9 26 32), losses := [{ target := 0, region := (rows 0 63 63 8 24 32), good := (rows 6 6 6 30 30 38) },{ target := 1, region := (rows 63 0 4 63 16 36), good := (rows 9 9 45 9 25 41) }] }

theorem profile8_node18 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,10] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,10] 2 profile8_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,10] 2 profile8_node18_cert).mp (by decide +kernel))

def profile8_node20_cert : Bound 6 := { allowed := (rows 0 0 0 0 3 0), upper := (rows 1 2 6 9 28 43), lower := (rows 1 2 6 9 28 43), losses := [] }

theorem profile8_node20 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,12,11] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,12,11] 2 profile8_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,12,11] 2 profile8_node20_cert).mp (by decide +kernel))

def profile8_node19_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node19 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,12] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,12] 2 (by decide) (choices 3) [11] profile8_node19_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1,12] (choices 3) [11] profile8_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node20

def profile8_node16_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node16 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1] 2 (by decide) (choices 2) [9,10,12] profile8_node16_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,1] (choices 2) [9,10,12] profile8_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node17
  · exact profile8_node18
  · exact profile8_node19

def profile8_node23_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 6 10 25 45), lower := (rows 1 2 6 10 25 45), losses := [] }

theorem profile8_node23 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,2,9,13] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,2,9,13] 2 profile8_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,2,9,13] 2 profile8_node23_cert).mp (by decide +kernel))

def profile8_node22_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node22 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,2,9] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,2,9] 2 (by decide) (choices 3) [13] profile8_node22_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,2,9] (choices 3) [13] profile8_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node23

def profile8_node21_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node21 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,2] 2 (by decide) (choices 2) [9] profile8_node21_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,2] (choices 2) [9] profile8_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node22

def profile8_node26_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 0), upper := (rows 1 2 6 12 25 43), lower := (rows 1 2 6 12 25 43), losses := [] }

theorem profile8_node26 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,4,9,11] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,4,9,11] 2 profile8_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,4,9,11] 2 profile8_node26_cert).mp (by decide +kernel))

def profile8_node25_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node25 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,4,9] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,4,9] 2 (by decide) (choices 3) [11] profile8_node25_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,4,9] (choices 3) [11] profile8_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node26

def profile8_node24_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node24 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,4] 2 (by decide) (choices 2) [9] profile8_node24_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2,4] (choices 2) [9] profile8_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node25

def profile8_node15_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node15 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2] 2 (by decide) (choices 1) [1,2,4] profile8_node15_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,2] (choices 1) [1,2,4] profile8_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node16
  · exact profile8_node21
  · exact profile8_node24

def profile8_node29_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 10), upper := (rows 1 2 12 9 19 46), lower := (rows 1 2 12 9 19 32), losses := [{ target := 0, region := (rows 0 63 12 8 16 44), good := (rows 2 2 46 46 18 34) },{ target := 3, region := (rows 63 63 4 0 63 32), good := (rows 19 19 23 19 19 51) }] }

theorem profile8_node29 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,3] 2 profile8_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,3] 2 profile8_node29_cert).mp (by decide +kernel))

def profile8_node31_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 2 12 9 22 43), lower := (rows 1 2 12 9 22 43), losses := [] }

theorem profile8_node31 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,6,11] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,6,11] 2 profile8_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,6,11] 2 profile8_node31_cert).mp (by decide +kernel))

def profile8_node30_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node30 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,6] 2 (by decide) (choices 3) [11] profile8_node30_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,6] (choices 3) [11] profile8_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node31

def profile8_node32_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 9 26 39), lower := (rows 1 2 12 9 26 32), losses := [{ target := 0, region := (rows 0 63 28 8 28 32), good := (rows 2 2 30 30 30 34) },{ target := 3, region := (rows 63 63 4 0 16 36), good := (rows 3 3 39 3 19 35) }] }

theorem profile8_node32 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,10] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,10] 2 profile8_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1,10] 2 profile8_node32_cert).mp (by decide +kernel))

def profile8_node28_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node28 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1] 2 (by decide) (choices 2) [3,6,10] profile8_node28_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,1] (choices 2) [3,6,10] profile8_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node29
  · exact profile8_node30
  · exact profile8_node32

def profile8_node34_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 2 12 10 19 45), lower := (rows 1 2 12 10 19 32), losses := [{ target := 1, region := (rows 63 0 12 8 16 44), good := (rows 1 1 45 45 17 33) },{ target := 3, region := (rows 63 63 4 0 63 32), good := (rows 19 19 23 19 19 51) }] }

theorem profile8_node34 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,3] 2 profile8_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,3] 2 profile8_node34_cert).mp (by decide +kernel))

def profile8_node36_cert : Bound 6 := { allowed := (rows 0 0 0 0 10 0), upper := (rows 1 2 12 10 21 43), lower := (rows 1 2 12 10 21 43), losses := [] }

theorem profile8_node36 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,5,11] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,5,11] 2 profile8_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,5,11] 2 profile8_node36_cert).mp (by decide +kernel))

def profile8_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node35 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,5] 2 (by decide) (choices 3) [11] profile8_node35_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,5] (choices 3) [11] profile8_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node36

def profile8_node37_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 10 25 39), lower := (rows 1 2 12 10 25 32), losses := [{ target := 1, region := (rows 63 0 28 8 28 32), good := (rows 1 1 29 29 29 33) },{ target := 3, region := (rows 63 63 4 0 16 36), good := (rows 3 3 39 3 19 35) }] }

theorem profile8_node37 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,9] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,9] 2 profile8_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2,9] 2 profile8_node37_cert).mp (by decide +kernel))

def profile8_node33_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node33 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2] 2 (by decide) (choices 2) [3,5,9] profile8_node33_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,2] (choices 2) [3,5,9] profile8_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node34
  · exact profile8_node35
  · exact profile8_node37

def profile8_node40_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 0), upper := (rows 1 2 12 12 19 43), lower := (rows 1 2 12 12 19 43), losses := [] }

theorem profile8_node40 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,4,3,11] 2 :=
  bound_sound (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,4,3,11] 2 profile8_node40_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,4,3,11] 2 profile8_node40_cert).mp (by decide +kernel))

def profile8_node39_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node39 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,4,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,4,3] 2 (by decide) (choices 3) [11] profile8_node39_route
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,4,3] (choices 3) [11] profile8_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node40

def profile8_node38_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node38 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,4] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,4] 2 (by decide) (choices 2) [3] profile8_node38_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8,4] (choices 2) [3] profile8_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node39

def profile8_node27_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node27 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8] 2 (by decide) (choices 1) [1,2,4] profile8_node27_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0,8] (choices 1) [1,2,4] profile8_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node28
  · exact profile8_node33
  · exact profile8_node38

def profile8_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node2 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0] 2 (by decide) (choices 1) [1,2,8] profile8_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0,0] (choices 1) [1,2,8] profile8_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node3
  · exact profile8_node15
  · exact profile8_node27

def profile8_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node1 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0] 2 (by decide) (choices 0) [0] profile8_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [0] (choices 0) [0] profile8_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node2

def profile8_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node0 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [] 2 (by decide) (choices 0) [0] profile8_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [] (choices 0) [0] profile8_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node1

theorem profile8 : Upper (D (n:=6) [2,2,9,10,16,24]) (R (n:=6) [2,2,9,10,16,24]) [] 2 := profile8_node0

def profile9_node5_cert : Bound 6 := { allowed := (rows 0 0 0 2 0 2), upper := (rows 1 2 5 41 50 38), lower := (rows 1 2 5 41 50 32), losses := [{ target := 0, region := (rows 0 63 4 8 60 36), good := (rows 2 2 54 58 50 50) }] }

theorem profile9_node5 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,33,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,33,34] 2 profile9_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,33,34] 2 profile9_node5_cert).mp (by decide +kernel))

def profile9_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node4 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,33] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,33] 2 (by decide) (choices 2) [34] profile9_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,33] (choices 2) [34] profile9_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node5

def profile9_node7_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 5 42 49 38), lower := (rows 1 2 5 42 49 32), losses := [{ target := 0, region := (rows 0 63 4 60 16 36), good := (rows 2 2 46 42 58 42) }] }

theorem profile9_node7 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,33] 2 profile9_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,33] 2 profile9_node7_cert).mp (by decide +kernel))

def profile9_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 42 50 37), lower := (rows 1 2 5 42 50 32), losses := [{ target := 0, region := (rows 0 63 4 56 56 32), good := (rows 2 2 6 58 58 58) }] }

theorem profile9_node8 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,34] 2 profile9_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,34] 2 profile9_node8_cert).mp (by decide +kernel))

def profile9_node10_cert : Bound 6 := { allowed := (rows 0 0 0 0 3 0), upper := (rows 1 2 5 42 52 35), lower := (rows 1 2 5 42 52 35), losses := [{ target := 0, region := (rows 0 63 4 56 16 32), good := (rows 2 2 6 42 62 42) }] }

theorem profile9_node10 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,36,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,36,3] 2 profile9_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,36,3] 2 profile9_node10_cert).mp (by decide +kernel))

def profile9_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node9 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,36] 2 (by decide) (choices 2) [3] profile9_node9_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34,36] (choices 2) [3] profile9_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node10

def profile9_node6_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node6 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34] 2 (by decide) (choices 2) [33,34,36] profile9_node6_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,34] (choices 2) [33,34,36] profile9_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node7
  · exact profile9_node8
  · exact profile9_node9

def profile9_node13_cert : Bound 6 := { allowed := (rows 0 0 0 3 0 0), upper := (rows 1 2 5 44 50 35), lower := (rows 1 2 5 44 50 35), losses := [{ target := 0, region := (rows 0 63 4 8 56 32), good := (rows 2 2 6 62 50 50) }] }

theorem profile9_node13 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,36,34,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,36,34,3] 2 profile9_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,36,34,3] 2 profile9_node13_cert).mp (by decide +kernel))

def profile9_node12_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node12 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,36,34] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,36,34] 2 (by decide) (choices 2) [3] profile9_node12_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,36,34] (choices 2) [3] profile9_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node13

def profile9_node11_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node11 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,36] 2 (by decide) (choices 2) [34] profile9_node11_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1,36] (choices 2) [34] profile9_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node12

def profile9_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node3 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1] 2 (by decide) (choices 2) [33,34,36] profile9_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,1] (choices 2) [33,34,36] profile9_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node4
  · exact profile9_node6
  · exact profile9_node11

def profile9_node16_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 2), upper := (rows 1 2 6 41 49 38), lower := (rows 1 2 6 41 49 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) },{ target := 1, region := (rows 63 0 4 56 56 32), good := (rows 1 1 5 57 57 57) }] }

theorem profile9_node16 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,33] 2 profile9_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,33] 2 profile9_node16_cert).mp (by decide +kernel))

def profile9_node17_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 2 6 41 50 37), lower := (rows 1 2 6 41 50 32), losses := [{ target := 0, region := (rows 0 63 63 8 56 32), good := (rows 6 6 6 62 54 54) },{ target := 1, region := (rows 63 0 4 60 16 36), good := (rows 1 1 45 41 57 41) }] }

theorem profile9_node17 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,34] 2 profile9_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,34] 2 profile9_node17_cert).mp (by decide +kernel))

def profile9_node19_cert : Bound 6 := { allowed := (rows 0 0 0 2 2 0), upper := (rows 1 2 6 41 52 35), lower := (rows 1 2 6 41 52 35), losses := [{ target := 0, region := (rows 0 63 63 8 56 32), good := (rows 6 6 6 62 54 54) }] }

theorem profile9_node19 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,36,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,36,3] 2 profile9_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,36,3] 2 profile9_node19_cert).mp (by decide +kernel))

def profile9_node18_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node18 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,36] 2 (by decide) (choices 2) [3] profile9_node18_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33,36] (choices 2) [3] profile9_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node19

def profile9_node15_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node15 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33] 2 (by decide) (choices 2) [33,34,36] profile9_node15_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,33] (choices 2) [33,34,36] profile9_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node16
  · exact profile9_node17
  · exact profile9_node18

def profile9_node21_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 2 6 42 49 37), lower := (rows 1 2 6 42 49 32), losses := [{ target := 0, region := (rows 0 63 63 56 16 32), good := (rows 6 6 6 46 62 46) },{ target := 1, region := (rows 63 0 4 8 60 36), good := (rows 1 1 53 57 49 49) }] }

theorem profile9_node21 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,34,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,34,33] 2 profile9_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,34,33] 2 profile9_node21_cert).mp (by decide +kernel))

def profile9_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node20 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,34] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,34] 2 (by decide) (choices 2) [33] profile9_node20_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,34] (choices 2) [33] profile9_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node21

def profile9_node24_cert : Bound 6 := { allowed := (rows 0 0 0 2 2 0), upper := (rows 1 2 6 44 49 35), lower := (rows 1 2 6 44 49 35), losses := [{ target := 0, region := (rows 0 63 63 56 16 32), good := (rows 6 6 6 46 62 46) }] }

theorem profile9_node24 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,36,33,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,36,33,3] 2 profile9_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,36,33,3] 2 profile9_node24_cert).mp (by decide +kernel))

def profile9_node23_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node23 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,36,33] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,36,33] 2 (by decide) (choices 2) [3] profile9_node23_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,36,33] (choices 2) [3] profile9_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node24

def profile9_node22_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node22 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,36] 2 (by decide) (choices 2) [33] profile9_node22_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2,36] (choices 2) [33] profile9_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node23

def profile9_node14_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node14 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2] 2 (by decide) (choices 2) [33,34,36] profile9_node14_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,2] (choices 2) [33,34,36] profile9_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node15
  · exact profile9_node20
  · exact profile9_node22

def profile9_node27_cert : Bound 6 := { allowed := (rows 0 0 0 32 0 2), upper := (rows 1 2 36 11 49 38), lower := (rows 1 2 36 11 49 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) },{ target := 1, region := (rows 63 0 52 8 52 32), good := (rows 1 1 53 9 53 53) }] }

theorem profile9_node27 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3,33] 2 profile9_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3,33] 2 profile9_node27_cert).mp (by decide +kernel))

def profile9_node28_cert : Bound 6 := { allowed := (rows 0 0 0 32 0 1), upper := (rows 1 2 36 11 50 37), lower := (rows 1 2 36 11 50 32), losses := [{ target := 0, region := (rows 0 63 52 8 52 32), good := (rows 2 2 54 10 54 54) },{ target := 1, region := (rows 63 0 63 8 16 63), good := (rows 37 37 37 45 53 37) }] }

theorem profile9_node28 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3,34] 2 profile9_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3,34] 2 profile9_node28_cert).mp (by decide +kernel))

def profile9_node29_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 11 52 35), lower := (rows 1 2 36 11 52 32), losses := [{ target := 0, region := (rows 0 63 52 8 52 32), good := (rows 2 2 54 10 54 54) },{ target := 1, region := (rows 63 0 52 8 52 32), good := (rows 1 1 53 9 53 53) },{ target := 5, region := (rows 63 63 4 63 16 0), good := (rows 11 11 15 11 31 11) }] }

theorem profile9_node29 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3,36] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3,36] 2 profile9_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3,36] 2 profile9_node29_cert).mp (by decide +kernel))

def profile9_node26_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node26 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3] 2 (by decide) (choices 2) [33,34,36] profile9_node26_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,3] (choices 2) [33,34,36] profile9_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node27
  · exact profile9_node28
  · exact profile9_node29

def profile9_node31_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 13 50 35), lower := (rows 1 2 36 13 50 32), losses := [{ target := 0, region := (rows 0 63 52 8 52 32), good := (rows 2 2 54 30 54 54) },{ target := 1, region := (rows 63 0 52 60 16 32), good := (rows 1 1 45 13 61 45) },{ target := 5, region := (rows 63 63 4 12 16 0), good := (rows 3 3 15 15 19 3) }] }

theorem profile9_node31 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,5,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,5,34] 2 profile9_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,5,34] 2 profile9_node31_cert).mp (by decide +kernel))

def profile9_node30_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node30 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,5] 2 (by decide) (choices 2) [34] profile9_node30_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,5] (choices 2) [34] profile9_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node31

def profile9_node33_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 14 49 35), lower := (rows 1 2 36 14 49 32), losses := [{ target := 0, region := (rows 0 63 52 60 16 32), good := (rows 2 2 46 14 62 46) },{ target := 1, region := (rows 63 0 52 8 52 32), good := (rows 1 1 53 29 53 53) },{ target := 5, region := (rows 63 63 4 12 16 0), good := (rows 3 3 15 15 19 3) }] }

theorem profile9_node33 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,6,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,6,33] 2 profile9_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,6,33] 2 profile9_node33_cert).mp (by decide +kernel))

def profile9_node32_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node32 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,6] 2 (by decide) (choices 2) [33] profile9_node32_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,6] (choices 2) [33] profile9_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node33

def profile9_node35_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 2), upper := (rows 1 2 36 41 19 38), lower := (rows 1 2 36 41 19 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) },{ target := 1, region := (rows 63 0 44 44 16 32), good := (rows 1 1 45 45 17 45) }] }

theorem profile9_node35 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,33,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,33,3] 2 profile9_node35_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,33,3] 2 profile9_node35_cert).mp (by decide +kernel))

def profile9_node36_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 41 22 35), lower := (rows 1 2 36 41 22 32), losses := [{ target := 0, region := (rows 0 63 44 8 60 32), good := (rows 2 2 54 62 22 54) },{ target := 1, region := (rows 63 0 44 44 16 32), good := (rows 1 1 45 45 29 45) },{ target := 5, region := (rows 63 63 4 8 20 0), good := (rows 3 3 23 11 23 3) }] }

theorem profile9_node36 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,33,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,33,6] 2 profile9_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,33,6] 2 profile9_node36_cert).mp (by decide +kernel))

def profile9_node34_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node34 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,33] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,33] 2 (by decide) (choices 2) [3,6] profile9_node34_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,33] (choices 2) [3,6] profile9_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node35
  · exact profile9_node36

def profile9_node38_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 2 36 42 19 37), lower := (rows 1 2 36 42 19 32), losses := [{ target := 0, region := (rows 0 63 44 44 16 32), good := (rows 2 2 46 46 18 46) },{ target := 1, region := (rows 63 0 63 8 16 63), good := (rows 37 37 37 45 53 37) }] }

theorem profile9_node38 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,34,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,34,3] 2 profile9_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,34,3] 2 profile9_node38_cert).mp (by decide +kernel))

def profile9_node39_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 42 21 35), lower := (rows 1 2 36 42 21 32), losses := [{ target := 0, region := (rows 0 63 44 44 16 32), good := (rows 2 2 46 46 30 46) },{ target := 1, region := (rows 63 0 44 8 60 32), good := (rows 1 1 53 61 21 53) },{ target := 5, region := (rows 63 63 4 8 20 0), good := (rows 3 3 23 11 23 3) }] }

theorem profile9_node39 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,34,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,34,5] 2 profile9_node39_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,34,5] 2 profile9_node39_cert).mp (by decide +kernel))

def profile9_node37_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node37 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,34] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,34] 2 (by decide) (choices 2) [3,5] profile9_node37_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,34] (choices 2) [3,5] profile9_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node38
  · exact profile9_node39

def profile9_node41_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 44 19 35), lower := (rows 1 2 36 44 19 32), losses := [{ target := 0, region := (rows 0 63 44 44 16 32), good := (rows 2 2 46 46 18 46) },{ target := 1, region := (rows 63 0 44 44 16 32), good := (rows 1 1 45 45 17 45) },{ target := 5, region := (rows 63 63 4 8 63 0), good := (rows 19 19 23 31 19 19) }] }

theorem profile9_node41 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,36,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,36,3] 2 profile9_node41_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,36,3] 2 profile9_node41_cert).mp (by decide +kernel))

def profile9_node40_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node40 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,36] 2 (by decide) (choices 2) [3] profile9_node40_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32,36] (choices 2) [3] profile9_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node41

def profile9_node25_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node25 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32] 2 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node25_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0,32] (choices 2) [3,5,6,33,34,36] profile9_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node26
  · exact profile9_node30
  · exact profile9_node32
  · exact profile9_node34
  · exact profile9_node37
  · exact profile9_node40

def profile9_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node2 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0] 2 (by decide) (choices 1) [1,2,32] profile9_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0,0] (choices 1) [1,2,32] profile9_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node3
  · exact profile9_node14
  · exact profile9_node25

def profile9_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node1 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0] 2 (by decide) (choices 0) [0] profile9_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [0] (choices 0) [0] profile9_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node2

def profile9_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node0 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [] 2 (by decide) (choices 0) [0] profile9_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [] (choices 0) [0] profile9_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node1

theorem profile9 : Upper (D (n:=6) [2,2,9,16,16,18]) (R (n:=6) [2,2,9,16,16,18]) [] 2 := profile9_node0

def profile10_node4_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 5 11 54 54), lower := (rows 1 2 5 11 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 20 36), good := (rows 2 2 54 10 18 34) }] }

theorem profile10_node4 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,3] 2 profile10_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,3] 2 profile10_node4_cert).mp (by decide +kernel))

def profile10_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 5 13 50 50), lower := (rows 1 2 5 13 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 63 63), good := (rows 50 50 54 62 50 50) },{ target := 1, region := (rows 63 0 63 63 16 32), good := (rows 13 13 13 13 29 45) }] }

theorem profile10_node5 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,5] 2 profile10_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,5] 2 profile10_node5_cert).mp (by decide +kernel))

def profile10_node7_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 5 14 49 50), lower := (rows 1 2 5 14 49 32), losses := [{ target := 0, region := (rows 0 63 4 12 16 48), good := (rows 2 2 14 14 50 34) }] }

theorem profile10_node7 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,6,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,6,33] 2 profile10_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,6,33] 2 profile10_node7_cert).mp (by decide +kernel))

def profile10_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 14 50 49), lower := (rows 1 2 5 14 50 32), losses := [{ target := 0, region := (rows 0 63 4 12 48 32), good := (rows 2 2 14 14 50 50) }] }

theorem profile10_node8 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,6,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,6,34] 2 profile10_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,6,34] 2 profile10_node8_cert).mp (by decide +kernel))

def profile10_node6_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node6 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,6] 2 (by decide) (choices 2) [33,34] profile10_node6_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,6] (choices 2) [33,34] profile10_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node7
  · exact profile10_node8

def profile10_node9_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 5 25 54 38), lower := (rows 1 2 5 25 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 20 36), good := (rows 2 2 54 26 18 34) },{ target := 1, region := (rows 63 0 63 24 16 32), good := (rows 5 5 5 29 29 37) }] }

theorem profile10_node9 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,17] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,17] 2 profile10_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,17] 2 profile10_node9_cert).mp (by decide +kernel))

def profile10_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 5 26 49 38), lower := (rows 1 2 5 26 49 32), losses := [{ target := 0, region := (rows 0 63 4 24 16 36), good := (rows 2 2 38 26 58 34) }] }

theorem profile10_node11 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,33] 2 profile10_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,33] 2 profile10_node11_cert).mp (by decide +kernel))

def profile10_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 26 50 37), lower := (rows 1 2 5 26 50 32), losses := [{ target := 0, region := (rows 0 63 4 56 48 32), good := (rows 2 2 6 26 58 58) }] }

theorem profile10_node12 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,34] 2 profile10_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,34] 2 profile10_node12_cert).mp (by decide +kernel))

def profile10_node14_cert : Bound 6 := { allowed := (rows 0 0 0 0 3 0), upper := (rows 1 2 5 26 52 35), lower := (rows 1 2 5 26 52 35), losses := [{ target := 0, region := (rows 0 63 4 24 16 32), good := (rows 2 2 6 26 62 34) }] }

theorem profile10_node14 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,36,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,36,3] 2 profile10_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,36,3] 2 profile10_node14_cert).mp (by decide +kernel))

def profile10_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node13 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,36] 2 (by decide) (choices 2) [3] profile10_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18,36] (choices 2) [3] profile10_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node14

def profile10_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node10 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18] 2 (by decide) (choices 2) [33,34,36] profile10_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,18] (choices 2) [33,34,36] profile10_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node11
  · exact profile10_node12
  · exact profile10_node13

def profile10_node17_cert : Bound 6 := { allowed := (rows 0 0 0 3 0 0), upper := (rows 1 2 5 28 50 35), lower := (rows 1 2 5 28 50 35), losses := [{ target := 0, region := (rows 0 63 4 8 48 32), good := (rows 2 2 6 30 50 50) }] }

theorem profile10_node17 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,20,34,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,20,34,3] 2 profile10_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,20,34,3] 2 profile10_node17_cert).mp (by decide +kernel))

def profile10_node16_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node16 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,20,34] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,20,34] 2 (by decide) (choices 2) [3] profile10_node16_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,20,34] (choices 2) [3] profile10_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node17

def profile10_node15_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node15 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,20] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,20] 2 (by decide) (choices 2) [34] profile10_node15_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,20] (choices 2) [34] profile10_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node16

def profile10_node20_cert : Bound 6 := { allowed := (rows 0 0 0 3 0 0), upper := (rows 1 2 5 56 19 38), lower := (rows 1 2 5 56 19 38), losses := [{ target := 0, region := (rows 0 63 4 8 16 36), good := (rows 2 2 38 58 18 38) }] }

theorem profile10_node20 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,3,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,3,6] 2 profile10_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,3,6] 2 profile10_node20_cert).mp (by decide +kernel))

def profile10_node19_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node19 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,3] 2 (by decide) (choices 2) [6] profile10_node19_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,3] (choices 2) [6] profile10_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node20

def profile10_node22_cert : Bound 6 := { allowed := (rows 0 0 0 3 0 0), upper := (rows 1 2 5 56 22 35), lower := (rows 1 2 5 56 22 35), losses := [{ target := 0, region := (rows 0 63 4 8 20 32), good := (rows 2 2 22 58 22 34) }] }

theorem profile10_node22 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,6,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,6,3] 2 profile10_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,6,3] 2 profile10_node22_cert).mp (by decide +kernel))

def profile10_node21_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node21 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,6] 2 (by decide) (choices 2) [3] profile10_node21_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48,6] (choices 2) [3] profile10_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node22

def profile10_node18_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node18 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48] 2 (by decide) (choices 2) [3,6] profile10_node18_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1,48] (choices 2) [3,6] profile10_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node19
  · exact profile10_node21

def profile10_node3_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile10_node3 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1] 2 (by decide) (choices 2) [3,5,6,17,18,20,48] profile10_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,1] (choices 2) [3,5,6,17,18,20,48] profile10_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node4
  · exact profile10_node5
  · exact profile10_node6
  · exact profile10_node9
  · exact profile10_node10
  · exact profile10_node15
  · exact profile10_node18

def profile10_node24_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 2 6 11 53 53), lower := (rows 1 2 6 11 16 32), losses := [{ target := 1, region := (rows 63 0 4 8 20 36), good := (rows 1 1 53 9 17 33) }] }

theorem profile10_node24 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,3] 2 profile10_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,3] 2 profile10_node24_cert).mp (by decide +kernel))

def profile10_node26_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 2), upper := (rows 1 2 6 13 49 50), lower := (rows 1 2 6 13 49 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 48), good := (rows 6 6 6 14 54 38) },{ target := 1, region := (rows 63 0 4 12 48 32), good := (rows 1 1 13 13 49 49) }] }

theorem profile10_node26 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,5,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,5,33] 2 profile10_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,5,33] 2 profile10_node26_cert).mp (by decide +kernel))

def profile10_node27_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 2 6 13 50 49), lower := (rows 1 2 6 13 50 32), losses := [{ target := 0, region := (rows 0 63 63 8 48 32), good := (rows 6 6 6 14 54 54) },{ target := 1, region := (rows 63 0 4 12 16 48), good := (rows 1 1 13 13 49 33) }] }

theorem profile10_node27 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,5,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,5,34] 2 profile10_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,5,34] 2 profile10_node27_cert).mp (by decide +kernel))

def profile10_node25_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node25 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,5] 2 (by decide) (choices 2) [33,34] profile10_node25_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,5] (choices 2) [33,34] profile10_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node26
  · exact profile10_node27

def profile10_node28_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 2 6 14 49 49), lower := (rows 1 2 6 14 16 32), losses := [{ target := 0, region := (rows 0 63 63 63 16 32), good := (rows 14 14 14 14 30 46) },{ target := 1, region := (rows 63 0 4 8 63 63), good := (rows 49 49 53 61 49 49) }] }

theorem profile10_node28 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,6] 2 profile10_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,6] 2 profile10_node28_cert).mp (by decide +kernel))

def profile10_node30_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 2), upper := (rows 1 2 6 25 49 38), lower := (rows 1 2 6 25 49 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 62 54 38) },{ target := 1, region := (rows 63 0 4 56 48 32), good := (rows 1 1 5 25 57 57) }] }

theorem profile10_node30 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,33] 2 profile10_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,33] 2 profile10_node30_cert).mp (by decide +kernel))

def profile10_node31_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 2 6 25 50 37), lower := (rows 1 2 6 25 50 32), losses := [{ target := 0, region := (rows 0 63 63 8 48 32), good := (rows 6 6 6 30 54 54) },{ target := 1, region := (rows 63 0 4 24 16 36), good := (rows 1 1 37 25 57 33) }] }

theorem profile10_node31 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,34] 2 profile10_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,34] 2 profile10_node31_cert).mp (by decide +kernel))

def profile10_node33_cert : Bound 6 := { allowed := (rows 0 0 0 2 2 0), upper := (rows 1 2 6 25 52 35), lower := (rows 1 2 6 25 52 35), losses := [{ target := 0, region := (rows 0 63 63 8 48 32), good := (rows 6 6 6 30 54 54) }] }

theorem profile10_node33 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,36,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,36,3] 2 profile10_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,36,3] 2 profile10_node33_cert).mp (by decide +kernel))

def profile10_node32_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node32 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,36] 2 (by decide) (choices 2) [3] profile10_node32_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17,36] (choices 2) [3] profile10_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node33

def profile10_node29_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node29 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17] 2 (by decide) (choices 2) [33,34,36] profile10_node29_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,17] (choices 2) [33,34,36] profile10_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node30
  · exact profile10_node31
  · exact profile10_node32

def profile10_node34_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 2 6 26 53 37), lower := (rows 1 2 6 26 16 32), losses := [{ target := 0, region := (rows 0 63 63 24 16 32), good := (rows 6 6 6 30 30 38) },{ target := 1, region := (rows 63 0 4 8 20 36), good := (rows 1 1 53 25 17 33) }] }

theorem profile10_node34 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,18] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,18] 2 profile10_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,18] 2 profile10_node34_cert).mp (by decide +kernel))

def profile10_node37_cert : Bound 6 := { allowed := (rows 0 0 0 2 2 0), upper := (rows 1 2 6 28 49 35), lower := (rows 1 2 6 28 49 35), losses := [{ target := 0, region := (rows 0 63 63 24 16 32), good := (rows 6 6 6 30 62 38) }] }

theorem profile10_node37 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,20,33,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,20,33,3] 2 profile10_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,20,33,3] 2 profile10_node37_cert).mp (by decide +kernel))

def profile10_node36_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node36 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,20,33] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,20,33] 2 (by decide) (choices 2) [3] profile10_node36_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,20,33] (choices 2) [3] profile10_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node37

def profile10_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node35 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,20] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,20] 2 (by decide) (choices 2) [33] profile10_node35_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,20] (choices 2) [33] profile10_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node36

def profile10_node40_cert : Bound 6 := { allowed := (rows 0 0 0 3 0 0), upper := (rows 1 2 6 56 19 37), lower := (rows 1 2 6 56 19 37), losses := [{ target := 1, region := (rows 63 0 4 8 16 36), good := (rows 1 1 37 57 17 37) }] }

theorem profile10_node40 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,3,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,3,5] 2 profile10_node40_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,3,5] 2 profile10_node40_cert).mp (by decide +kernel))

def profile10_node39_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node39 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,3] 2 (by decide) (choices 2) [5] profile10_node39_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,3] (choices 2) [5] profile10_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node40

def profile10_node42_cert : Bound 6 := { allowed := (rows 0 0 0 3 0 0), upper := (rows 1 2 6 56 21 35), lower := (rows 1 2 6 56 21 35), losses := [{ target := 1, region := (rows 63 0 4 8 20 32), good := (rows 1 1 21 57 21 33) }] }

theorem profile10_node42 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,5,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,5,3] 2 profile10_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,5,3] 2 profile10_node42_cert).mp (by decide +kernel))

def profile10_node41_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node41 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,5] 2 (by decide) (choices 2) [3] profile10_node41_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48,5] (choices 2) [3] profile10_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node42

def profile10_node38_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node38 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48] 2 (by decide) (choices 2) [3,5] profile10_node38_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2,48] (choices 2) [3,5] profile10_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node39
  · exact profile10_node41

def profile10_node23_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile10_node23 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2] 2 (by decide) (choices 2) [3,5,6,17,18,20,48] profile10_node23_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,2] (choices 2) [3,5,6,17,18,20,48] profile10_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node24
  · exact profile10_node25
  · exact profile10_node28
  · exact profile10_node29
  · exact profile10_node34
  · exact profile10_node35
  · exact profile10_node38

def profile10_node45_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 20 11 49 38), lower := (rows 1 2 20 11 49 32), losses := [{ target := 0, region := (rows 0 63 20 8 16 52), good := (rows 2 2 54 10 54 34) }] }

theorem profile10_node45 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3,33] 2 profile10_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3,33] 2 profile10_node45_cert).mp (by decide +kernel))

def profile10_node46_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 11 50 37), lower := (rows 1 2 20 11 50 32), losses := [{ target := 0, region := (rows 0 63 52 8 48 32), good := (rows 2 2 22 10 54 54) }] }

theorem profile10_node46 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3,34] 2 profile10_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3,34] 2 profile10_node46_cert).mp (by decide +kernel))

def profile10_node47_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 11 52 35), lower := (rows 1 2 20 11 52 32), losses := [{ target := 0, region := (rows 0 63 52 8 48 32), good := (rows 2 2 22 10 54 54) },{ target := 1, region := (rows 63 0 52 8 48 32), good := (rows 1 1 21 9 53 53) }] }

theorem profile10_node47 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3,36] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3,36] 2 profile10_node47_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3,36] 2 profile10_node47_cert).mp (by decide +kernel))

def profile10_node44_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node44 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3] 2 (by decide) (choices 2) [33,34,36] profile10_node44_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,3] (choices 2) [33,34,36] profile10_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node45
  · exact profile10_node46
  · exact profile10_node47

def profile10_node49_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 13 50 35), lower := (rows 1 2 20 13 50 32), losses := [{ target := 0, region := (rows 0 63 52 8 48 32), good := (rows 2 2 22 14 54 54) },{ target := 1, region := (rows 63 0 20 28 16 32), good := (rows 1 1 29 13 61 33) }] }

theorem profile10_node49 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,5,34] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,5,34] 2 profile10_node49_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,5,34] 2 profile10_node49_cert).mp (by decide +kernel))

def profile10_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node48 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,5] 2 (by decide) (choices 2) [34] profile10_node48_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,5] (choices 2) [34] profile10_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node49

def profile10_node51_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 14 49 35), lower := (rows 1 2 20 14 49 32), losses := [{ target := 0, region := (rows 0 63 20 28 16 32), good := (rows 2 2 30 14 62 34) },{ target := 1, region := (rows 63 0 52 8 48 32), good := (rows 1 1 21 13 53 53) }] }

theorem profile10_node51 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,6,33] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,6,33] 2 profile10_node51_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,6,33] 2 profile10_node51_cert).mp (by decide +kernel))

def profile10_node50_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node50 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,6] 2 (by decide) (choices 2) [33] profile10_node50_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,6] (choices 2) [33] profile10_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node51

def profile10_node53_cert : Bound 6 := { allowed := (rows 0 0 0 2 0 2), upper := (rows 1 2 20 41 19 38), lower := (rows 1 2 20 41 19 32), losses := [{ target := 0, region := (rows 0 63 20 8 16 52), good := (rows 2 2 54 42 54 34) }] }

theorem profile10_node53 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,33,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,33,3] 2 profile10_node53_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,33,3] 2 profile10_node53_cert).mp (by decide +kernel))

def profile10_node54_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 41 22 35), lower := (rows 1 2 20 41 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 62 22 54) },{ target := 1, region := (rows 63 0 20 40 16 32), good := (rows 1 1 21 41 21 41) }] }

theorem profile10_node54 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,33,6] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,33,6] 2 profile10_node54_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,33,6] 2 profile10_node54_cert).mp (by decide +kernel))

def profile10_node52_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node52 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,33] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,33] 2 (by decide) (choices 2) [3,6] profile10_node52_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,33] (choices 2) [3,6] profile10_node52_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node53
  · exact profile10_node54

def profile10_node56_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 42 19 37), lower := (rows 1 2 20 42 19 32), losses := [{ target := 0, region := (rows 0 63 20 40 16 32), good := (rows 2 2 22 42 22 42) }] }

theorem profile10_node56 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,34,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,34,3] 2 profile10_node56_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,34,3] 2 profile10_node56_cert).mp (by decide +kernel))

def profile10_node57_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 20 42 21 35), lower := (rows 1 2 20 42 21 32), losses := [{ target := 0, region := (rows 0 63 20 40 16 32), good := (rows 2 2 22 42 22 42) },{ target := 1, region := (rows 63 0 63 8 63 32), good := (rows 21 21 21 61 21 53) }] }

theorem profile10_node57 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,34,5] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,34,5] 2 profile10_node57_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,34,5] 2 profile10_node57_cert).mp (by decide +kernel))

def profile10_node55_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node55 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,34] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,34] 2 (by decide) (choices 2) [3,5] profile10_node55_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,34] (choices 2) [3,5] profile10_node55_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node56
  · exact profile10_node57

def profile10_node60_cert : Bound 6 := { allowed := (rows 0 0 0 3 0 0), upper := (rows 1 2 20 44 19 35), lower := (rows 1 2 20 44 19 35), losses := [] }

theorem profile10_node60 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,36,3,3] 2 :=
  bound_sound (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,36,3,3] 2 profile10_node60_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,36,3,3] 2 profile10_node60_cert).mp (by decide +kernel))

def profile10_node59_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node59 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,36,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,36,3] 2 (by decide) (choices 2) [3] profile10_node59_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,36,3] (choices 2) [3] profile10_node59_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node60

def profile10_node58_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node58 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,36] 2 (by decide) (choices 2) [3] profile10_node58_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16,36] (choices 2) [3] profile10_node58_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node59

def profile10_node43_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node43 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16] 2 (by decide) (choices 2) [3,5,6,33,34,36] profile10_node43_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0,16] (choices 2) [3,5,6,33,34,36] profile10_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node44
  · exact profile10_node48
  · exact profile10_node50
  · exact profile10_node52
  · exact profile10_node55
  · exact profile10_node58

def profile10_node2_route : Route 6 := (fun mask => match mask with | 32 => (16,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile10_node2 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0] 2 (by decide) (choices 1) [1,2,16] profile10_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0,0] (choices 1) [1,2,16] profile10_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node3
  · exact profile10_node23
  · exact profile10_node43

def profile10_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node1 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0] 2 (by decide) (choices 0) [0] profile10_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [0] (choices 0) [0] profile10_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node2

def profile10_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node0 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [] 2 (by decide) (choices 0) [0] profile10_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [] (choices 0) [0] profile10_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node1

theorem profile10 : Upper (D (n:=6) [2,2,9,16,17,17]) (R (n:=6) [2,2,9,16,17,17]) [] 2 := profile10_node0

def profile11_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 5 11 52 38), lower := (rows 1 2 5 11 52 32), losses := [{ target := 0, region := (rows 0 63 4 8 20 52), good := (rows 2 2 54 10 54 34) },{ target := 1, region := (rows 63 0 63 8 48 32), good := (rows 5 5 5 13 53 53) },{ target := 2, region := (rows 63 63 0 63 16 32), good := (rows 11 11 11 11 59 43) }] }

theorem profile11_node5 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,3,36] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,3,36] 2 profile11_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,3,36] 2 profile11_node5_cert).mp (by decide +kernel))

def profile11_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node4 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,3] 2 (by decide) (choices 2) [36] profile11_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,3] (choices 2) [36] profile11_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node5

def profile11_node7_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 5 13 50 38), lower := (rows 1 2 5 13 50 32), losses := [{ target := 0, region := (rows 0 63 4 8 60 44), good := (rows 2 2 54 62 50 50) },{ target := 1, region := (rows 63 0 63 63 16 32), good := (rows 13 13 13 13 61 45) },{ target := 2, region := (rows 63 63 0 8 48 32), good := (rows 3 3 3 11 51 51) }] }

theorem profile11_node7 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,5,34] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,5,34] 2 profile11_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,5,34] 2 profile11_node7_cert).mp (by decide +kernel))

def profile11_node6_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node6 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,5] 2 (by decide) (choices 2) [34] profile11_node6_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,5] (choices 2) [34] profile11_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node7

def profile11_node9_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 5 14 49 38), lower := (rows 1 2 5 14 49 32), losses := [{ target := 0, region := (rows 0 63 4 12 16 44), good := (rows 2 2 46 46 50 34) },{ target := 1, region := (rows 63 0 63 8 48 32), good := (rows 5 5 5 13 53 53) },{ target := 2, region := (rows 63 63 0 8 48 32), good := (rows 3 3 3 11 51 51) }] }

theorem profile11_node9 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,33] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,33] 2 profile11_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,33] 2 profile11_node9_cert).mp (by decide +kernel))

def profile11_node10_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 5 14 50 37), lower := (rows 1 2 5 14 50 32), losses := [{ target := 0, region := (rows 0 63 4 12 48 32), good := (rows 2 2 14 14 50 50) },{ target := 1, region := (rows 63 0 63 8 16 63), good := (rows 37 37 37 45 53 37) },{ target := 2, region := (rows 63 63 0 8 48 32), good := (rows 3 3 3 11 51 51) }] }

theorem profile11_node10 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,34] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,34] 2 profile11_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,34] 2 profile11_node10_cert).mp (by decide +kernel))

def profile11_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 4), upper := (rows 1 2 5 14 52 35), lower := (rows 1 2 5 14 52 35), losses := [{ target := 0, region := (rows 0 63 4 28 16 32), good := (rows 2 2 14 14 62 34) },{ target := 1, region := (rows 63 0 63 8 48 32), good := (rows 5 5 5 13 53 53) }] }

theorem profile11_node12 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,36,3] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,36,3] 2 profile11_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,36,3] 2 profile11_node12_cert).mp (by decide +kernel))

def profile11_node11_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node11 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,36] 2 (by decide) (choices 2) [3] profile11_node11_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6,36] (choices 2) [3] profile11_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node12

def profile11_node8_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node8 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6] 2 (by decide) (choices 2) [33,34,36] profile11_node8_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,6] (choices 2) [33,34,36] profile11_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node9
  · exact profile11_node10
  · exact profile11_node11

def profile11_node14_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 5 41 22 38), lower := (rows 1 2 5 41 22 32), losses := [{ target := 0, region := (rows 0 63 4 8 20 52), good := (rows 2 2 54 42 54 34) },{ target := 1, region := (rows 63 0 63 40 16 32), good := (rows 5 5 5 45 21 45) },{ target := 2, region := (rows 63 63 0 40 16 32), good := (rows 3 3 3 43 19 43) }] }

theorem profile11_node14 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,33,6] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,33,6] 2 profile11_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,33,6] 2 profile11_node14_cert).mp (by decide +kernel))

def profile11_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node13 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,33] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,33] 2 (by decide) (choices 2) [6] profile11_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,33] (choices 2) [6] profile11_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node14

def profile11_node16_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 5 42 21 38), lower := (rows 1 2 5 42 21 32), losses := [{ target := 0, region := (rows 0 63 4 60 16 52), good := (rows 2 2 46 42 62 42) },{ target := 1, region := (rows 63 0 63 8 63 32), good := (rows 21 21 21 61 21 53) },{ target := 2, region := (rows 63 63 0 40 16 32), good := (rows 3 3 3 43 19 43) }] }

theorem profile11_node16 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,34,5] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,34,5] 2 profile11_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,34,5] 2 profile11_node16_cert).mp (by decide +kernel))

def profile11_node17_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 5 42 22 37), lower := (rows 1 2 5 42 22 32), losses := [{ target := 0, region := (rows 0 63 4 40 20 32), good := (rows 2 2 22 42 22 42) },{ target := 1, region := (rows 63 0 63 8 16 63), good := (rows 37 37 37 45 53 37) },{ target := 2, region := (rows 63 63 0 40 16 32), good := (rows 3 3 3 43 19 43) }] }

theorem profile11_node17 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,34,6] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,34,6] 2 profile11_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,34,6] 2 profile11_node17_cert).mp (by decide +kernel))

def profile11_node15_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node15 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,34] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,34] 2 (by decide) (choices 2) [5,6] profile11_node15_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,34] (choices 2) [5,6] profile11_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node16
  · exact profile11_node17

def profile11_node19_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 5 44 19 38), lower := (rows 1 2 5 44 19 32), losses := [{ target := 0, region := (rows 0 63 4 12 16 44), good := (rows 2 2 46 46 18 34) },{ target := 1, region := (rows 63 0 63 40 16 32), good := (rows 5 5 5 45 21 45) },{ target := 2, region := (rows 63 63 0 8 63 32), good := (rows 19 19 19 59 19 51) }] }

theorem profile11_node19 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36,3] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36,3] 2 profile11_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36,3] 2 profile11_node19_cert).mp (by decide +kernel))

def profile11_node21_cert : Bound 6 := { allowed := (rows 0 0 0 1 0 4), upper := (rows 1 2 5 44 22 35), lower := (rows 1 2 5 44 22 35), losses := [{ target := 0, region := (rows 0 63 4 8 28 32), good := (rows 2 2 22 62 22 34) },{ target := 1, region := (rows 63 0 63 40 16 32), good := (rows 5 5 5 45 21 45) }] }

theorem profile11_node21 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36,6,3] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36,6,3] 2 profile11_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36,6,3] 2 profile11_node21_cert).mp (by decide +kernel))

def profile11_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node20 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36,6] 2 (by decide) (choices 2) [3] profile11_node20_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36,6] (choices 2) [3] profile11_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node21

def profile11_node18_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node18 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36] 2 (by decide) (choices 2) [3,6] profile11_node18_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1,36] (choices 2) [3,6] profile11_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node19
  · exact profile11_node20

def profile11_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node3 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1] 2 (by decide) (choices 2) [3,5,6,33,34,36] profile11_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,1] (choices 2) [3,5,6,33,34,36] profile11_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node4
  · exact profile11_node6
  · exact profile11_node8
  · exact profile11_node13
  · exact profile11_node15
  · exact profile11_node18

def profile11_node24_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 6 11 52 37), lower := (rows 1 2 6 11 52 32), losses := [{ target := 0, region := (rows 0 63 63 8 48 32), good := (rows 6 6 6 14 54 54) },{ target := 1, region := (rows 63 0 4 8 20 52), good := (rows 1 1 53 9 53 33) },{ target := 2, region := (rows 63 63 0 63 16 32), good := (rows 11 11 11 11 59 43) }] }

theorem profile11_node24 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,3,36] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,3,36] 2 profile11_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,3,36] 2 profile11_node24_cert).mp (by decide +kernel))

def profile11_node23_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node23 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,3] 2 (by decide) (choices 2) [36] profile11_node23_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,3] (choices 2) [36] profile11_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node24

def profile11_node26_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 6 13 49 38), lower := (rows 1 2 6 13 49 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) },{ target := 1, region := (rows 63 0 4 12 48 32), good := (rows 1 1 13 13 49 49) },{ target := 2, region := (rows 63 63 0 8 48 32), good := (rows 3 3 3 11 51 51) }] }

theorem profile11_node26 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,33] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,33] 2 profile11_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,33] 2 profile11_node26_cert).mp (by decide +kernel))

def profile11_node27_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 6 13 50 37), lower := (rows 1 2 6 13 50 32), losses := [{ target := 0, region := (rows 0 63 63 8 48 32), good := (rows 6 6 6 14 54 54) },{ target := 1, region := (rows 63 0 4 12 16 44), good := (rows 1 1 45 45 49 33) },{ target := 2, region := (rows 63 63 0 8 48 32), good := (rows 3 3 3 11 51 51) }] }

theorem profile11_node27 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,34] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,34] 2 profile11_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,34] 2 profile11_node27_cert).mp (by decide +kernel))

def profile11_node29_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 4), upper := (rows 1 2 6 13 52 35), lower := (rows 1 2 6 13 52 35), losses := [{ target := 0, region := (rows 0 63 63 8 48 32), good := (rows 6 6 6 14 54 54) },{ target := 1, region := (rows 63 0 4 28 16 32), good := (rows 1 1 13 13 61 33) }] }

theorem profile11_node29 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,36,3] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,36,3] 2 profile11_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,36,3] 2 profile11_node29_cert).mp (by decide +kernel))

def profile11_node28_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node28 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,36] 2 (by decide) (choices 2) [3] profile11_node28_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5,36] (choices 2) [3] profile11_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node29

def profile11_node25_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node25 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5] 2 (by decide) (choices 2) [33,34,36] profile11_node25_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,5] (choices 2) [33,34,36] profile11_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node26
  · exact profile11_node27
  · exact profile11_node28

def profile11_node31_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 6 14 49 37), lower := (rows 1 2 6 14 49 32), losses := [{ target := 0, region := (rows 0 63 63 63 16 32), good := (rows 14 14 14 14 62 46) },{ target := 1, region := (rows 63 0 4 8 60 44), good := (rows 1 1 53 61 49 49) },{ target := 2, region := (rows 63 63 0 8 48 32), good := (rows 3 3 3 11 51 51) }] }

theorem profile11_node31 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,6,33] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,6,33] 2 profile11_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,6,33] 2 profile11_node31_cert).mp (by decide +kernel))

def profile11_node30_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node30 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,6] 2 (by decide) (choices 2) [33] profile11_node30_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,6] (choices 2) [33] profile11_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node31

def profile11_node33_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 6 41 21 38), lower := (rows 1 2 6 41 21 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) },{ target := 1, region := (rows 63 0 4 40 20 32), good := (rows 1 1 21 41 21 41) },{ target := 2, region := (rows 63 63 0 40 16 32), good := (rows 3 3 3 43 19 43) }] }

theorem profile11_node33 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,33,5] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,33,5] 2 profile11_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,33,5] 2 profile11_node33_cert).mp (by decide +kernel))

def profile11_node34_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 6 41 22 37), lower := (rows 1 2 6 41 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 62 22 54) },{ target := 1, region := (rows 63 0 4 60 16 52), good := (rows 1 1 45 41 61 41) },{ target := 2, region := (rows 63 63 0 40 16 32), good := (rows 3 3 3 43 19 43) }] }

theorem profile11_node34 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,33,6] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,33,6] 2 profile11_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,33,6] 2 profile11_node34_cert).mp (by decide +kernel))

def profile11_node32_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node32 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,33] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,33] 2 (by decide) (choices 2) [5,6] profile11_node32_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,33] (choices 2) [5,6] profile11_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node33
  · exact profile11_node34

def profile11_node36_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 6 42 21 37), lower := (rows 1 2 6 42 21 32), losses := [{ target := 0, region := (rows 0 63 63 40 16 32), good := (rows 6 6 6 46 22 46) },{ target := 1, region := (rows 63 0 4 8 20 52), good := (rows 1 1 53 41 53 33) },{ target := 2, region := (rows 63 63 0 40 16 32), good := (rows 3 3 3 43 19 43) }] }

theorem profile11_node36 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,34,5] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,34,5] 2 profile11_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,34,5] 2 profile11_node36_cert).mp (by decide +kernel))

def profile11_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node35 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,34] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,34] 2 (by decide) (choices 2) [5] profile11_node35_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,34] (choices 2) [5] profile11_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node36

def profile11_node38_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 6 44 19 37), lower := (rows 1 2 6 44 19 32), losses := [{ target := 0, region := (rows 0 63 63 40 16 32), good := (rows 6 6 6 46 22 46) },{ target := 1, region := (rows 63 0 4 12 16 44), good := (rows 1 1 45 45 17 33) },{ target := 2, region := (rows 63 63 0 8 63 32), good := (rows 19 19 19 59 19 51) }] }

theorem profile11_node38 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36,3] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36,3] 2 profile11_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36,3] 2 profile11_node38_cert).mp (by decide +kernel))

def profile11_node40_cert : Bound 6 := { allowed := (rows 0 0 0 2 0 4), upper := (rows 1 2 6 44 21 35), lower := (rows 1 2 6 44 21 35), losses := [{ target := 0, region := (rows 0 63 63 40 16 32), good := (rows 6 6 6 46 22 46) },{ target := 1, region := (rows 63 0 4 8 28 32), good := (rows 1 1 21 61 21 33) }] }

theorem profile11_node40 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36,5,3] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36,5,3] 2 profile11_node40_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36,5,3] 2 profile11_node40_cert).mp (by decide +kernel))

def profile11_node39_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node39 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36,5] 2 (by decide) (choices 2) [3] profile11_node39_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36,5] (choices 2) [3] profile11_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node40

def profile11_node37_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node37 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36] 2 (by decide) (choices 2) [3,5] profile11_node37_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2,36] (choices 2) [3,5] profile11_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node38
  · exact profile11_node39

def profile11_node22_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node22 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2] 2 (by decide) (choices 2) [3,5,6,33,34,36] profile11_node22_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,2] (choices 2) [3,5,6,33,34,36] profile11_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node23
  · exact profile11_node25
  · exact profile11_node30
  · exact profile11_node32
  · exact profile11_node35
  · exact profile11_node37

def profile11_node43_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 36 11 21 38), lower := (rows 1 2 36 11 21 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) },{ target := 1, region := (rows 63 0 36 8 52 32), good := (rows 1 1 53 9 21 53) },{ target := 2, region := (rows 63 63 0 63 16 32), good := (rows 11 11 43 11 27 43) }] }

theorem profile11_node43 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,3,5] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,3,5] 2 profile11_node43_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,3,5] 2 profile11_node43_cert).mp (by decide +kernel))

def profile11_node44_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 36 11 22 37), lower := (rows 1 2 36 11 22 32), losses := [{ target := 0, region := (rows 0 63 36 8 52 32), good := (rows 2 2 54 10 22 54) },{ target := 1, region := (rows 63 0 63 8 16 63), good := (rows 37 37 37 45 53 37) },{ target := 2, region := (rows 63 63 0 63 16 32), good := (rows 11 11 43 11 27 43) }] }

theorem profile11_node44 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,3,6] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,3,6] 2 profile11_node44_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,3,6] 2 profile11_node44_cert).mp (by decide +kernel))

def profile11_node42_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node42 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,3] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,3] 2 (by decide) (choices 2) [5,6] profile11_node42_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,3] (choices 2) [5,6] profile11_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node43
  · exact profile11_node44

def profile11_node46_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 36 13 19 38), lower := (rows 1 2 36 13 19 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) },{ target := 1, region := (rows 63 0 36 44 16 32), good := (rows 1 1 45 13 17 45) },{ target := 2, region := (rows 63 63 0 8 63 32), good := (rows 19 19 51 27 19 51) }] }

theorem profile11_node46 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,5,3] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,5,3] 2 profile11_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,5,3] 2 profile11_node46_cert).mp (by decide +kernel))

def profile11_node47_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 13 22 35), lower := (rows 1 2 36 13 22 32), losses := [{ target := 0, region := (rows 0 63 36 8 60 32), good := (rows 2 2 54 30 22 54) },{ target := 1, region := (rows 63 0 36 60 16 32), good := (rows 1 1 45 13 29 45) },{ target := 2, region := (rows 63 63 0 8 16 63), good := (rows 35 35 35 43 51 35) }] }

theorem profile11_node47 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,5,6] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,5,6] 2 profile11_node47_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,5,6] 2 profile11_node47_cert).mp (by decide +kernel))

def profile11_node45_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node45 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,5] 2 (by decide) (choices 2) [3,6] profile11_node45_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,5] (choices 2) [3,6] profile11_node45_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node46
  · exact profile11_node47

def profile11_node49_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 36 14 19 37), lower := (rows 1 2 36 14 19 32), losses := [{ target := 0, region := (rows 0 63 36 44 16 32), good := (rows 2 2 46 14 18 46) },{ target := 1, region := (rows 63 0 63 8 16 63), good := (rows 37 37 37 45 53 37) },{ target := 2, region := (rows 63 63 0 8 63 32), good := (rows 19 19 51 27 19 51) }] }

theorem profile11_node49 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,6,3] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,6,3] 2 profile11_node49_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,6,3] 2 profile11_node49_cert).mp (by decide +kernel))

def profile11_node50_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 14 21 35), lower := (rows 1 2 36 14 21 32), losses := [{ target := 0, region := (rows 0 63 36 60 16 32), good := (rows 2 2 46 14 30 46) },{ target := 1, region := (rows 63 0 36 8 60 32), good := (rows 1 1 53 29 21 53) },{ target := 2, region := (rows 63 63 0 8 16 63), good := (rows 35 35 35 43 51 35) }] }

theorem profile11_node50 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,6,5] 2 :=
  bound_sound (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,6,5] 2 profile11_node50_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,6,5] 2 profile11_node50_cert).mp (by decide +kernel))

def profile11_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node48 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,6] 2 (by decide) (choices 2) [3,5] profile11_node48_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32,6] (choices 2) [3,5] profile11_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node49
  · exact profile11_node50

def profile11_node41_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node41 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32] 2 (by decide) (choices 2) [3,5,6] profile11_node41_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0,32] (choices 2) [3,5,6] profile11_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node42
  · exact profile11_node45
  · exact profile11_node48

def profile11_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node2 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0] 2 (by decide) (choices 1) [1,2,32] profile11_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0,0] (choices 1) [1,2,32] profile11_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node3
  · exact profile11_node22
  · exact profile11_node41

def profile11_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node1 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0] 2 (by decide) (choices 0) [0] profile11_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [0] (choices 0) [0] profile11_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node2

def profile11_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node0 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [] 2 (by decide) (choices 0) [0] profile11_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [] (choices 0) [0] profile11_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node1

theorem profile11 : Upper (D (n:=6) [2,2,10,16,16,17]) (R (n:=6) [2,2,10,16,16,17]) [] 2 := profile11_node0

def profile12_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 5 13 22 38), lower := (rows 1 2 5 13 22 32), losses := [{ target := 0, region := (rows 0 63 4 8 28 60), good := (rows 2 2 54 62 54 34) },{ target := 1, region := (rows 63 0 63 63 16 32), good := (rows 13 13 13 13 29 45) }] }

theorem profile12_node5 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,5,6] 2 :=
  bound_sound (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,5,6] 2 profile12_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,5,6] 2 profile12_node5_cert).mp (by decide +kernel))

def profile12_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node4 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,5] 2 (by decide) (choices 2) [6] profile12_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,5] (choices 2) [6] profile12_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node5

def profile12_node7_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 5 14 21 38), lower := (rows 1 2 5 14 21 32), losses := [{ target := 0, region := (rows 0 63 4 28 16 60), good := (rows 2 2 46 46 62 34) },{ target := 1, region := (rows 63 0 63 8 63 32), good := (rows 21 21 21 29 21 53) }] }

theorem profile12_node7 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,6,5] 2 :=
  bound_sound (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,6,5] 2 profile12_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,6,5] 2 profile12_node7_cert).mp (by decide +kernel))

def profile12_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 5 14 22 37), lower := (rows 1 2 5 14 22 32), losses := [{ target := 0, region := (rows 0 63 4 28 28 32), good := (rows 2 2 30 30 30 34) },{ target := 1, region := (rows 63 0 63 8 16 63), good := (rows 37 37 37 45 53 37) }] }

theorem profile12_node8 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,6,6] 2 :=
  bound_sound (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,6,6] 2 profile12_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,6,6] 2 profile12_node8_cert).mp (by decide +kernel))

def profile12_node6_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node6 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,6] 2 (by decide) (choices 2) [5,6] profile12_node6_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1,6] (choices 2) [5,6] profile12_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node7
  · exact profile12_node8

def profile12_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node3 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1] 2 (by decide) (choices 2) [5,6] profile12_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,1] (choices 2) [5,6] profile12_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node4
  · exact profile12_node6

def profile12_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 6 13 21 38), lower := (rows 1 2 6 13 21 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) },{ target := 1, region := (rows 63 0 4 28 28 32), good := (rows 1 1 29 29 29 33) }] }

theorem profile12_node11 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,5,5] 2 :=
  bound_sound (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,5,5] 2 profile12_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,5,5] 2 profile12_node11_cert).mp (by decide +kernel))

def profile12_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 6 13 22 37), lower := (rows 1 2 6 13 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 30 22 54) },{ target := 1, region := (rows 63 0 4 28 16 60), good := (rows 1 1 45 45 61 33) }] }

theorem profile12_node12 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,5,6] 2 :=
  bound_sound (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,5,6] 2 profile12_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,5,6] 2 profile12_node12_cert).mp (by decide +kernel))

def profile12_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node10 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,5] 2 := by
  apply routed_branch (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,5] 2 (by decide) (choices 2) [5,6] profile12_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,5] (choices 2) [5,6] profile12_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node11
  · exact profile12_node12

def profile12_node14_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 6 14 21 37), lower := (rows 1 2 6 14 21 32), losses := [{ target := 0, region := (rows 0 63 63 63 16 32), good := (rows 14 14 14 14 30 46) },{ target := 1, region := (rows 63 0 4 8 28 60), good := (rows 1 1 53 61 53 33) }] }

theorem profile12_node14 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,6,5] 2 :=
  bound_sound (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,6,5] 2 profile12_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,6,5] 2 profile12_node14_cert).mp (by decide +kernel))

def profile12_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node13 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,6] 2 := by
  apply routed_branch (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,6] 2 (by decide) (choices 2) [5] profile12_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2,6] (choices 2) [5] profile12_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node14

def profile12_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node9 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2] 2 (by decide) (choices 2) [5,6] profile12_node9_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0,2] (choices 2) [5,6] profile12_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node10
  · exact profile12_node13

def profile12_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node2 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0] 2 (by decide) (choices 1) [1,2] profile12_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0,0] (choices 1) [1,2] profile12_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node3
  · exact profile12_node9

def profile12_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node1 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0] 2 (by decide) (choices 0) [0] profile12_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [0] (choices 0) [0] profile12_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node2

def profile12_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node0 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [] 2 := by
  apply routed_branch (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [] 2 (by decide) (choices 0) [0] profile12_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [] (choices 0) [0] profile12_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node1

theorem profile12 : Upper (D (n:=6) [2,2,11,16,16,16]) (R (n:=6) [2,2,11,16,16,16]) [] 2 := profile12_node0

def profile13_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 10 19 46), lower := (rows 1 2 5 10 19 32), losses := [] }

theorem profile13_node5 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2,3] 2 profile13_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2,3] 2 profile13_node5_cert).mp (by decide +kernel))

def profile13_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 10 22 43), lower := (rows 1 2 5 10 22 32), losses := [{ target := 0, region := (rows 0 63 4 63 20 32), good := (rows 10 10 30 10 30 42) }] }

theorem profile13_node6 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2,6] 2 :=
  bound_sound (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2,6] 2 profile13_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2,6] 2 profile13_node6_cert).mp (by decide +kernel))

def profile13_node7_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 10 26 39), lower := (rows 1 2 5 10 26 32), losses := [{ target := 0, region := (rows 0 63 4 63 63 32), good := (rows 26 26 30 26 26 58) }] }

theorem profile13_node7 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2,10] 2 :=
  bound_sound (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2,10] 2 profile13_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2,10] 2 profile13_node7_cert).mp (by decide +kernel))

def profile13_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node4 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2] 2 (by decide) (choices 2) [3,6,10] profile13_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1,2] (choices 2) [3,6,10] profile13_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node5
  · exact profile13_node6
  · exact profile13_node7

def profile13_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node3 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1] 2 (by decide) (choices 1) [2] profile13_node3_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,1] (choices 1) [2] profile13_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node4

def profile13_node10_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 9 19 46), lower := (rows 1 2 6 9 19 32), losses := [] }

theorem profile13_node10 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1,3] 2 profile13_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1,3] 2 profile13_node10_cert).mp (by decide +kernel))

def profile13_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 9 22 43), lower := (rows 1 2 6 9 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 30 22 54) }] }

theorem profile13_node11 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1,6] 2 :=
  bound_sound (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1,6] 2 profile13_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1,6] 2 profile13_node11_cert).mp (by decide +kernel))

def profile13_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 9 26 39), lower := (rows 1 2 6 9 26 32), losses := [{ target := 0, region := (rows 0 63 63 8 24 32), good := (rows 6 6 6 30 30 38) }] }

theorem profile13_node12 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1,10] 2 :=
  bound_sound (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1,10] 2 profile13_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1,10] 2 profile13_node12_cert).mp (by decide +kernel))

def profile13_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node9 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1] 2 (by decide) (choices 2) [3,6,10] profile13_node9_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,1] (choices 2) [3,6,10] profile13_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node10
  · exact profile13_node11
  · exact profile13_node12

def profile13_node14_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 10 19 45), lower := (rows 1 2 6 10 19 32), losses := [] }

theorem profile13_node14 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2,3] 2 profile13_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2,3] 2 profile13_node14_cert).mp (by decide +kernel))

def profile13_node15_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 10 21 43), lower := (rows 1 2 6 10 21 32), losses := [{ target := 1, region := (rows 63 0 4 8 20 32), good := (rows 1 1 21 9 21 33) }] }

theorem profile13_node15 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2,5] 2 :=
  bound_sound (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2,5] 2 profile13_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2,5] 2 profile13_node15_cert).mp (by decide +kernel))

def profile13_node16_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 10 25 39), lower := (rows 1 2 6 10 25 32), losses := [{ target := 1, region := (rows 63 0 4 8 24 32), good := (rows 1 1 5 25 25 33) }] }

theorem profile13_node16 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2,9] 2 :=
  bound_sound (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2,9] 2 profile13_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2,9] 2 profile13_node16_cert).mp (by decide +kernel))

def profile13_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node13 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2] 2 (by decide) (choices 2) [3,5,9] profile13_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,2] (choices 2) [3,5,9] profile13_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node14
  · exact profile13_node15
  · exact profile13_node16

def profile13_node18_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 12 19 43), lower := (rows 1 2 6 12 19 32), losses := [] }

theorem profile13_node18 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,4,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,4,3] 2 profile13_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,4,3] 2 profile13_node18_cert).mp (by decide +kernel))

def profile13_node17_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node17 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,4] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,4] 2 (by decide) (choices 2) [3] profile13_node17_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2,4] (choices 2) [3] profile13_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node18

def profile13_node8_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node8 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2] 2 (by decide) (choices 1) [1,2,4] profile13_node8_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,2] (choices 1) [1,2,4] profile13_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node9
  · exact profile13_node13
  · exact profile13_node17

def profile13_node21_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 12 10 19 39), lower := (rows 1 2 12 10 19 32), losses := [] }

theorem profile13_node21 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,8,2,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,8,2,3] 2 profile13_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,8,2,3] 2 profile13_node21_cert).mp (by decide +kernel))

def profile13_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node20 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,8,2] 2 (by decide) (choices 2) [3] profile13_node20_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,8,2] (choices 2) [3] profile13_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node21

def profile13_node19_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node19 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,8] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,8] 2 (by decide) (choices 1) [2] profile13_node19_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0,8] (choices 1) [2] profile13_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node20

def profile13_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node2 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0] 2 (by decide) (choices 1) [1,2,8] profile13_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0,0] (choices 1) [1,2,8] profile13_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node3
  · exact profile13_node8
  · exact profile13_node19

def profile13_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node1 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0] 2 (by decide) (choices 0) [0] profile13_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [0] (choices 0) [0] profile13_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node2

def profile13_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node0 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [] 2 (by decide) (choices 0) [0] profile13_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [] (choices 0) [0] profile13_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node1

theorem profile13 : Upper (D (n:=6) [2,3,9,9,16,24]) (R (n:=6) [2,3,9,9,16,24]) [] 2 := profile13_node0

def profile14_node4_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 5 11 54 38), lower := (rows 1 2 5 11 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 20 36), good := (rows 2 2 54 10 18 34) }] }

theorem profile14_node4 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,3] 2 profile14_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,3] 2 profile14_node4_cert).mp (by decide +kernel))

def profile14_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 14 50 35), lower := (rows 1 2 5 14 50 32), losses := [{ target := 0, region := (rows 0 63 4 12 48 32), good := (rows 2 2 14 14 50 50) }] }

theorem profile14_node6 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,6,34] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,6,34] 2 profile14_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,6,34] 2 profile14_node6_cert).mp (by decide +kernel))

def profile14_node5_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node5 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,6] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,6] 2 (by decide) (choices 2) [34] profile14_node5_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,6] (choices 2) [34] profile14_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node6

def profile14_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 2), upper := (rows 1 2 5 42 19 38), lower := (rows 1 2 5 42 19 32), losses := [{ target := 0, region := (rows 0 63 4 44 16 36), good := (rows 2 2 46 42 18 42) }] }

theorem profile14_node8 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,34,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,34,3] 2 profile14_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,34,3] 2 profile14_node8_cert).mp (by decide +kernel))

def profile14_node9_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 42 22 35), lower := (rows 1 2 5 42 22 32), losses := [{ target := 0, region := (rows 0 63 4 40 20 32), good := (rows 2 2 22 42 22 42) }] }

theorem profile14_node9 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,34,6] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,34,6] 2 profile14_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,34,6] 2 profile14_node9_cert).mp (by decide +kernel))

def profile14_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node7 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,34] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,34] 2 (by decide) (choices 2) [3,6] profile14_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1,34] (choices 2) [3,6] profile14_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile14_node8
  · exact profile14_node9

def profile14_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node3 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1] 2 (by decide) (choices 2) [3,6,34] profile14_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,1] (choices 2) [3,6,34] profile14_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node4
  · exact profile14_node5
  · exact profile14_node7

def profile14_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 2 2), upper := (rows 1 2 6 11 49 38), lower := (rows 1 2 6 11 49 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) }] }

theorem profile14_node12 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,33] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,33] 2 profile14_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,33] 2 profile14_node12_cert).mp (by decide +kernel))

def profile14_node13_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 11 50 37), lower := (rows 1 2 6 11 50 32), losses := [{ target := 0, region := (rows 0 63 63 8 48 32), good := (rows 6 6 6 14 54 54) }] }

theorem profile14_node13 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,34] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,34] 2 profile14_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,34] 2 profile14_node13_cert).mp (by decide +kernel))

def profile14_node15_cert : Bound 6 := { allowed := (rows 0 0 0 0 3 0), upper := (rows 1 2 6 11 52 35), lower := (rows 1 2 6 11 52 35), losses := [] }

theorem profile14_node15 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,36,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,36,3] 2 profile14_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,36,3] 2 profile14_node15_cert).mp (by decide +kernel))

def profile14_node14_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node14 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,36] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,36] 2 (by decide) (choices 2) [3] profile14_node14_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3,36] (choices 2) [3] profile14_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node15

def profile14_node11_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node11 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3] 2 (by decide) (choices 2) [33,34,36] profile14_node11_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,3] (choices 2) [33,34,36] profile14_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node12
  · exact profile14_node13
  · exact profile14_node14

def profile14_node17_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 13 50 35), lower := (rows 1 2 6 13 50 32), losses := [{ target := 0, region := (rows 0 63 63 8 48 32), good := (rows 6 6 6 14 54 54) },{ target := 1, region := (rows 63 0 4 12 16 32), good := (rows 1 1 13 13 49 33) }] }

theorem profile14_node17 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,5,34] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,5,34] 2 profile14_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,5,34] 2 profile14_node17_cert).mp (by decide +kernel))

def profile14_node16_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node16 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,5] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,5] 2 (by decide) (choices 2) [34] profile14_node16_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,5] (choices 2) [34] profile14_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node17

def profile14_node19_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 14 49 35), lower := (rows 1 2 6 14 49 32), losses := [{ target := 0, region := (rows 0 63 63 63 16 32), good := (rows 14 14 14 14 62 46) },{ target := 1, region := (rows 63 0 4 8 48 32), good := (rows 1 1 5 13 49 49) }] }

theorem profile14_node19 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,6,33] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,6,33] 2 profile14_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,6,33] 2 profile14_node19_cert).mp (by decide +kernel))

def profile14_node18_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node18 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,6] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,6] 2 (by decide) (choices 2) [33] profile14_node18_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,6] (choices 2) [33] profile14_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node19

def profile14_node21_cert : Bound 6 := { allowed := (rows 0 0 0 2 0 2), upper := (rows 1 2 6 41 19 38), lower := (rows 1 2 6 41 19 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) }] }

theorem profile14_node21 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,33,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,33,3] 2 profile14_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,33,3] 2 profile14_node21_cert).mp (by decide +kernel))

def profile14_node22_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 41 22 35), lower := (rows 1 2 6 41 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 62 22 54) },{ target := 1, region := (rows 63 0 4 40 16 32), good := (rows 1 1 5 41 21 41) }] }

theorem profile14_node22 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,33,6] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,33,6] 2 profile14_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,33,6] 2 profile14_node22_cert).mp (by decide +kernel))

def profile14_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node20 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,33] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,33] 2 (by decide) (choices 2) [3,6] profile14_node20_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,33] (choices 2) [3,6] profile14_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile14_node21
  · exact profile14_node22

def profile14_node24_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 42 19 37), lower := (rows 1 2 6 42 19 32), losses := [{ target := 0, region := (rows 0 63 63 40 16 32), good := (rows 6 6 6 46 22 46) }] }

theorem profile14_node24 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,34,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,34,3] 2 profile14_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,34,3] 2 profile14_node24_cert).mp (by decide +kernel))

def profile14_node25_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 42 21 35), lower := (rows 1 2 6 42 21 32), losses := [{ target := 0, region := (rows 0 63 63 40 16 32), good := (rows 6 6 6 46 22 46) },{ target := 1, region := (rows 63 0 4 8 20 32), good := (rows 1 1 21 41 21 33) }] }

theorem profile14_node25 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,34,5] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,34,5] 2 profile14_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,34,5] 2 profile14_node25_cert).mp (by decide +kernel))

def profile14_node23_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node23 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,34] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,34] 2 (by decide) (choices 2) [3,5] profile14_node23_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,34] (choices 2) [3,5] profile14_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile14_node24
  · exact profile14_node25

def profile14_node28_cert : Bound 6 := { allowed := (rows 0 0 0 3 0 0), upper := (rows 1 2 6 44 19 35), lower := (rows 1 2 6 44 19 35), losses := [] }

theorem profile14_node28 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,36,3,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,36,3,3] 2 profile14_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,36,3,3] 2 profile14_node28_cert).mp (by decide +kernel))

def profile14_node27_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node27 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,36,3] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,36,3] 2 (by decide) (choices 2) [3] profile14_node27_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,36,3] (choices 2) [3] profile14_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node28

def profile14_node26_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node26 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,36] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,36] 2 (by decide) (choices 2) [3] profile14_node26_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2,36] (choices 2) [3] profile14_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node27

def profile14_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node10 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2] 2 (by decide) (choices 2) [3,5,6,33,34,36] profile14_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,2] (choices 2) [3,5,6,33,34,36] profile14_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node11
  · exact profile14_node16
  · exact profile14_node18
  · exact profile14_node20
  · exact profile14_node23
  · exact profile14_node26

def profile14_node31_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 11 19 38), lower := (rows 1 2 36 11 19 32), losses := [] }

theorem profile14_node31 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,3,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,3,3] 2 profile14_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,3,3] 2 profile14_node31_cert).mp (by decide +kernel))

def profile14_node32_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 11 22 35), lower := (rows 1 2 36 11 22 32), losses := [{ target := 0, region := (rows 0 63 36 8 52 32), good := (rows 2 2 54 10 22 54) }] }

theorem profile14_node32 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,3,6] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,3,6] 2 profile14_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,3,6] 2 profile14_node32_cert).mp (by decide +kernel))

def profile14_node30_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node30 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,3] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,3] 2 (by decide) (choices 2) [3,6] profile14_node30_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,3] (choices 2) [3,6] profile14_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile14_node31
  · exact profile14_node32

def profile14_node34_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 36 14 19 35), lower := (rows 1 2 36 14 19 32), losses := [{ target := 0, region := (rows 0 63 36 44 16 32), good := (rows 2 2 46 14 18 46) }] }

theorem profile14_node34 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,6,3] 2 :=
  bound_sound (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,6,3] 2 profile14_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,6,3] 2 profile14_node34_cert).mp (by decide +kernel))

def profile14_node33_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node33 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,6] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,6] 2 (by decide) (choices 2) [3] profile14_node33_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32,6] (choices 2) [3] profile14_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node34

def profile14_node29_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node29 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32] 2 (by decide) (choices 2) [3,6] profile14_node29_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0,32] (choices 2) [3,6] profile14_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile14_node30
  · exact profile14_node33

def profile14_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node2 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0] 2 (by decide) (choices 1) [1,2,32] profile14_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0,0] (choices 1) [1,2,32] profile14_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node3
  · exact profile14_node10
  · exact profile14_node29

def profile14_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node1 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0] 2 (by decide) (choices 0) [0] profile14_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [0] (choices 0) [0] profile14_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node2

def profile14_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node0 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [] 2 := by
  apply routed_branch (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [] 2 (by decide) (choices 0) [0] profile14_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [] (choices 0) [0] profile14_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node1

theorem profile14 : Upper (D (n:=6) [2,3,9,16,16,17]) (R (n:=6) [2,3,9,16,16,17]) [] 2 := profile14_node0

def profile15_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 5 11 22 38), lower := (rows 1 2 5 11 22 32), losses := [{ target := 0, region := (rows 0 63 4 8 20 52), good := (rows 2 2 54 10 54 34) },{ target := 2, region := (rows 63 63 0 63 16 32), good := (rows 11 11 11 11 27 43) }] }

theorem profile15_node5 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,3,6] 2 :=
  bound_sound (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,3,6] 2 profile15_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,3,6] 2 profile15_node5_cert).mp (by decide +kernel))

def profile15_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile15_node4 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,3] 2 := by
  apply routed_branch (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,3] 2 (by decide) (choices 2) [6] profile15_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,3] (choices 2) [6] profile15_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node5

def profile15_node7_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 5 14 19 38), lower := (rows 1 2 5 14 19 32), losses := [{ target := 0, region := (rows 0 63 4 12 16 44), good := (rows 2 2 46 46 18 34) },{ target := 2, region := (rows 63 63 0 8 63 32), good := (rows 19 19 19 27 19 51) }] }

theorem profile15_node7 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,6,3] 2 :=
  bound_sound (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,6,3] 2 profile15_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,6,3] 2 profile15_node7_cert).mp (by decide +kernel))

def profile15_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 14 22 35), lower := (rows 1 2 5 14 22 32), losses := [{ target := 0, region := (rows 0 63 4 28 28 32), good := (rows 2 2 30 30 30 34) },{ target := 2, region := (rows 63 63 0 8 16 63), good := (rows 35 35 35 43 51 35) }] }

theorem profile15_node8 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,6,6] 2 :=
  bound_sound (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,6,6] 2 profile15_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,6,6] 2 profile15_node8_cert).mp (by decide +kernel))

def profile15_node6_route : Route 6 := (fun mask => (mask,id))

theorem profile15_node6 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,6] 2 := by
  apply routed_branch (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,6] 2 (by decide) (choices 2) [3,6] profile15_node6_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1,6] (choices 2) [3,6] profile15_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile15_node7
  · exact profile15_node8

def profile15_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile15_node3 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1] 2 := by
  apply routed_branch (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1] 2 (by decide) (choices 2) [3,6] profile15_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,1] (choices 2) [3,6] profile15_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile15_node4
  · exact profile15_node6

def profile15_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 6 11 21 38), lower := (rows 1 2 6 11 21 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) },{ target := 1, region := (rows 63 0 4 8 20 32), good := (rows 1 1 21 9 21 33) },{ target := 2, region := (rows 63 63 0 63 16 32), good := (rows 11 11 11 11 27 43) }] }

theorem profile15_node11 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,3,5] 2 :=
  bound_sound (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,3,5] 2 profile15_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,3,5] 2 profile15_node11_cert).mp (by decide +kernel))

def profile15_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 6 11 22 37), lower := (rows 1 2 6 11 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 30 22 54) },{ target := 1, region := (rows 63 0 4 8 16 52), good := (rows 1 1 37 9 53 33) },{ target := 2, region := (rows 63 63 0 63 16 32), good := (rows 11 11 11 11 27 43) }] }

theorem profile15_node12 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,3,6] 2 :=
  bound_sound (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,3,6] 2 profile15_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,3,6] 2 profile15_node12_cert).mp (by decide +kernel))

def profile15_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile15_node10 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,3] 2 := by
  apply routed_branch (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,3] 2 (by decide) (choices 2) [5,6] profile15_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,3] (choices 2) [5,6] profile15_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile15_node11
  · exact profile15_node12

def profile15_node14_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 6), upper := (rows 1 2 6 13 19 38), lower := (rows 1 2 6 13 19 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 38 38 38 46 54 38) },{ target := 1, region := (rows 63 0 4 12 16 32), good := (rows 1 1 13 13 17 33) },{ target := 2, region := (rows 63 63 0 8 63 32), good := (rows 19 19 19 27 19 51) }] }

theorem profile15_node14 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,5,3] 2 :=
  bound_sound (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,5,3] 2 profile15_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,5,3] 2 profile15_node14_cert).mp (by decide +kernel))

def profile15_node15_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 13 22 35), lower := (rows 1 2 6 13 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 30 22 54) },{ target := 1, region := (rows 63 0 4 28 16 32), good := (rows 1 1 13 13 29 33) },{ target := 2, region := (rows 63 63 0 8 16 63), good := (rows 35 35 35 43 51 35) }] }

theorem profile15_node15 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,5,6] 2 :=
  bound_sound (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,5,6] 2 profile15_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,5,6] 2 profile15_node15_cert).mp (by decide +kernel))

def profile15_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile15_node13 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,5] 2 := by
  apply routed_branch (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,5] 2 (by decide) (choices 2) [3,6] profile15_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,5] (choices 2) [3,6] profile15_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile15_node14
  · exact profile15_node15

def profile15_node17_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 2 6 14 19 37), lower := (rows 1 2 6 14 19 32), losses := [{ target := 0, region := (rows 0 63 63 63 16 32), good := (rows 14 14 14 14 30 46) },{ target := 1, region := (rows 63 0 4 8 16 44), good := (rows 1 1 37 45 17 33) },{ target := 2, region := (rows 63 63 0 8 63 32), good := (rows 19 19 19 27 19 51) }] }

theorem profile15_node17 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,6,3] 2 :=
  bound_sound (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,6,3] 2 profile15_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,6,3] 2 profile15_node17_cert).mp (by decide +kernel))

def profile15_node18_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 14 21 35), lower := (rows 1 2 6 14 21 32), losses := [{ target := 0, region := (rows 0 63 63 63 16 32), good := (rows 14 14 14 14 30 46) },{ target := 1, region := (rows 63 0 4 8 28 32), good := (rows 1 1 21 29 21 33) },{ target := 2, region := (rows 63 63 0 8 16 63), good := (rows 35 35 35 43 51 35) }] }

theorem profile15_node18 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,6,5] 2 :=
  bound_sound (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,6,5] 2 profile15_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,6,5] 2 profile15_node18_cert).mp (by decide +kernel))

def profile15_node16_route : Route 6 := (fun mask => (mask,id))

theorem profile15_node16 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,6] 2 := by
  apply routed_branch (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,6] 2 (by decide) (choices 2) [3,5] profile15_node16_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2,6] (choices 2) [3,5] profile15_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile15_node17
  · exact profile15_node18

def profile15_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile15_node9 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2] 2 (by decide) (choices 2) [3,5,6] profile15_node9_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0,2] (choices 2) [3,5,6] profile15_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node10
  · exact profile15_node13
  · exact profile15_node16

def profile15_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile15_node2 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0] 2 (by decide) (choices 1) [1,2] profile15_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0,0] (choices 1) [1,2] profile15_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile15_node3
  · exact profile15_node9

def profile15_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile15_node1 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0] 2 (by decide) (choices 0) [0] profile15_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [0] (choices 0) [0] profile15_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node2

def profile15_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile15_node0 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [] 2 := by
  apply routed_branch (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [] 2 (by decide) (choices 0) [0] profile15_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [] (choices 0) [0] profile15_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node1

theorem profile15 : Upper (D (n:=6) [2,3,10,16,16,16]) (R (n:=6) [2,3,10,16,16,16]) [] 2 := profile15_node0

def profile16_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 11 19 38), lower := (rows 1 2 6 11 19 32), losses := [] }

theorem profile16_node5 : Upper (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,3,3] 2 :=
  bound_sound (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,3,3] 2 profile16_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,3,3] 2 profile16_node5_cert).mp (by decide +kernel))

def profile16_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 11 22 35), lower := (rows 1 2 6 11 22 32), losses := [{ target := 0, region := (rows 0 63 63 8 63 32), good := (rows 22 22 22 30 22 54) }] }

theorem profile16_node6 : Upper (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,3,6] 2 :=
  bound_sound (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,3,6] 2 profile16_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,3,6] 2 profile16_node6_cert).mp (by decide +kernel))

def profile16_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile16_node4 : Upper (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,3] 2 := by
  apply routed_branch (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,3] 2 (by decide) (choices 2) [3,6] profile16_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,3] (choices 2) [3,6] profile16_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile16_node5
  · exact profile16_node6

def profile16_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 14 19 35), lower := (rows 1 2 6 14 19 32), losses := [{ target := 0, region := (rows 0 63 63 63 16 32), good := (rows 14 14 14 14 30 46) }] }

theorem profile16_node8 : Upper (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,6,3] 2 :=
  bound_sound (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,6,3] 2 profile16_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,6,3] 2 profile16_node8_cert).mp (by decide +kernel))

def profile16_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile16_node7 : Upper (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,6] 2 := by
  apply routed_branch (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,6] 2 (by decide) (choices 2) [3] profile16_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2,6] (choices 2) [3] profile16_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile16_node8

def profile16_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile16_node3 : Upper (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2] 2 (by decide) (choices 2) [3,6] profile16_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0,2] (choices 2) [3,6] profile16_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile16_node4
  · exact profile16_node7

def profile16_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile16_node2 : Upper (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0] 2 (by decide) (choices 1) [2] profile16_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0,0] (choices 1) [2] profile16_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile16_node3

def profile16_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile16_node1 : Upper (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0] 2 (by decide) (choices 0) [0] profile16_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [0] (choices 0) [0] profile16_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile16_node2

def profile16_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile16_node0 : Upper (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [] 2 := by
  apply routed_branch (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [] 2 (by decide) (choices 0) [0] profile16_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [] (choices 0) [0] profile16_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile16_node1

theorem profile16 : Upper (D (n:=6) [2,4,9,16,16,16]) (R (n:=6) [2,4,9,16,16,16]) [] 2 := profile16_node0

def profile17_node0_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 63 63 63 63 63 63), lower := (rows 1 2 4 8 16 32), losses := [] }

theorem profile17_node0 : Upper (D (n:=6) [2,9,9,9,9,25]) (R (n:=6) [2,9,9,9,9,25]) [] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,9,25]) (R (n:=6) [2,9,9,9,9,25]) [] 2 profile17_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,9,25]) (R (n:=6) [2,9,9,9,9,25]) [] 2 profile17_node0_cert).mp (by decide +kernel))

theorem profile17 : Upper (D (n:=6) [2,9,9,9,9,25]) (R (n:=6) [2,9,9,9,9,25]) [] 2 := profile17_node0

def profile18_node0_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 17), upper := (rows 31 31 31 31 31 63), lower := (rows 1 2 4 8 16 32), losses := [] }

theorem profile18_node0 : Upper (D (n:=6) [2,9,9,9,10,24]) (R (n:=6) [2,9,9,9,10,24]) [] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,10,24]) (R (n:=6) [2,9,9,9,10,24]) [] 2 profile18_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,10,24]) (R (n:=6) [2,9,9,9,10,24]) [] 2 profile18_node0_cert).mp (by decide +kernel))

theorem profile18 : Upper (D (n:=6) [2,9,9,9,10,24]) (R (n:=6) [2,9,9,9,10,24]) [] 2 := profile18_node0

def profile19_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 5 40 50 44), lower := (rows 1 3 5 40 50 32), losses := [] }

theorem profile19_node5 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32,34] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32,34] 2 profile19_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32,34] 2 profile19_node5_cert).mp (by decide +kernel))

def profile19_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 5 40 52 42), lower := (rows 1 3 5 40 52 32), losses := [] }

theorem profile19_node6 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32,36] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32,36] 2 profile19_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32,36] 2 profile19_node6_cert).mp (by decide +kernel))

def profile19_node7_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 5 40 56 38), lower := (rows 1 3 5 40 56 32), losses := [] }

theorem profile19_node7 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32,40] 2 profile19_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32,40] 2 profile19_node7_cert).mp (by decide +kernel))

def profile19_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node4 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32] 2 (by decide) (choices 2) [34,36,40] profile19_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1,32] (choices 2) [34,36,40] profile19_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node5
  · exact profile19_node6
  · exact profile19_node7

def profile19_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node3 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1] 2 (by decide) (choices 1) [32] profile19_node3_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,1] (choices 1) [32] profile19_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node4

def profile19_node10_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 3 6 40 49 44), lower := (rows 1 3 6 40 49 32), losses := [] }

theorem profile19_node10 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32,33] 2 profile19_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32,33] 2 profile19_node10_cert).mp (by decide +kernel))

def profile19_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 6 40 52 41), lower := (rows 1 3 6 40 52 32), losses := [] }

theorem profile19_node11 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32,36] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32,36] 2 profile19_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32,36] 2 profile19_node11_cert).mp (by decide +kernel))

def profile19_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 6 40 56 37), lower := (rows 1 3 6 40 56 32), losses := [] }

theorem profile19_node12 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32,40] 2 profile19_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32,40] 2 profile19_node12_cert).mp (by decide +kernel))

def profile19_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node9 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32] 2 (by decide) (choices 2) [33,36,40] profile19_node9_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2,32] (choices 2) [33,36,40] profile19_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node10
  · exact profile19_node11
  · exact profile19_node12

def profile19_node8_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node8 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2] 2 (by decide) (choices 1) [32] profile19_node8_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,2] (choices 1) [32] profile19_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node9

def profile19_node15_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 3 12 40 49 38), lower := (rows 1 3 12 40 49 32), losses := [] }

theorem profile19_node15 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32,33] 2 profile19_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32,33] 2 profile19_node15_cert).mp (by decide +kernel))

def profile19_node16_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 12 40 50 37), lower := (rows 1 3 12 40 50 32), losses := [] }

theorem profile19_node16 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32,34] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32,34] 2 profile19_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32,34] 2 profile19_node16_cert).mp (by decide +kernel))

def profile19_node17_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 12 40 52 35), lower := (rows 1 3 12 40 52 32), losses := [] }

theorem profile19_node17 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32,36] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32,36] 2 profile19_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32,36] 2 profile19_node17_cert).mp (by decide +kernel))

def profile19_node14_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node14 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32] 2 (by decide) (choices 2) [33,34,36] profile19_node14_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8,32] (choices 2) [33,34,36] profile19_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node15
  · exact profile19_node16
  · exact profile19_node17

def profile19_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node13 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8] 2 (by decide) (choices 1) [32] profile19_node13_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,8] (choices 1) [32] profile19_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node14

def profile19_node20_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 36 9 50 44), lower := (rows 1 3 36 9 50 32), losses := [] }

theorem profile19_node20 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1,34] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1,34] 2 profile19_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1,34] 2 profile19_node20_cert).mp (by decide +kernel))

def profile19_node21_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 36 9 52 42), lower := (rows 1 3 36 9 52 32), losses := [] }

theorem profile19_node21 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1,36] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1,36] 2 profile19_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1,36] 2 profile19_node21_cert).mp (by decide +kernel))

def profile19_node22_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 36 9 56 38), lower := (rows 1 3 36 9 56 32), losses := [] }

theorem profile19_node22 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1,40] 2 profile19_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1,40] 2 profile19_node22_cert).mp (by decide +kernel))

def profile19_node19_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node19 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1] 2 (by decide) (choices 2) [34,36,40] profile19_node19_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,1] (choices 2) [34,36,40] profile19_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node20
  · exact profile19_node21
  · exact profile19_node22

def profile19_node24_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 3 36 10 49 44), lower := (rows 1 3 36 10 49 32), losses := [] }

theorem profile19_node24 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2,33] 2 profile19_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2,33] 2 profile19_node24_cert).mp (by decide +kernel))

def profile19_node25_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 36 10 52 41), lower := (rows 1 3 36 10 52 32), losses := [] }

theorem profile19_node25 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2,36] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2,36] 2 profile19_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2,36] 2 profile19_node25_cert).mp (by decide +kernel))

def profile19_node26_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 36 10 56 37), lower := (rows 1 3 36 10 56 32), losses := [] }

theorem profile19_node26 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2,40] 2 profile19_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2,40] 2 profile19_node26_cert).mp (by decide +kernel))

def profile19_node23_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node23 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2] 2 (by decide) (choices 2) [33,36,40] profile19_node23_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,2] (choices 2) [33,36,40] profile19_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node24
  · exact profile19_node25
  · exact profile19_node26

def profile19_node28_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 3 36 12 49 42), lower := (rows 1 3 36 12 49 32), losses := [] }

theorem profile19_node28 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4,33] 2 profile19_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4,33] 2 profile19_node28_cert).mp (by decide +kernel))

def profile19_node29_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 36 12 50 41), lower := (rows 1 3 36 12 50 32), losses := [] }

theorem profile19_node29 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4,34] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4,34] 2 profile19_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4,34] 2 profile19_node29_cert).mp (by decide +kernel))

def profile19_node30_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 36 12 56 35), lower := (rows 1 3 36 12 56 32), losses := [] }

theorem profile19_node30 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4,40] 2 profile19_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4,40] 2 profile19_node30_cert).mp (by decide +kernel))

def profile19_node27_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node27 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4] 2 (by decide) (choices 2) [33,34,40] profile19_node27_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,4] (choices 2) [33,34,40] profile19_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node28
  · exact profile19_node29
  · exact profile19_node30

def profile19_node32_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 3 36 40 19 44), lower := (rows 1 3 36 40 19 32), losses := [] }

theorem profile19_node32 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,3] 2 profile19_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,3] 2 profile19_node32_cert).mp (by decide +kernel))

def profile19_node33_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 3 36 40 21 42), lower := (rows 1 3 36 40 21 32), losses := [] }

theorem profile19_node33 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,5] 2 profile19_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,5] 2 profile19_node33_cert).mp (by decide +kernel))

def profile19_node34_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 36 40 22 41), lower := (rows 1 3 36 40 22 32), losses := [{ target := 5, region := (rows 63 63 4 8 20 0), good := (rows 3 3 23 11 23 3) }] }

theorem profile19_node34 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,6] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,6] 2 profile19_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,6] 2 profile19_node34_cert).mp (by decide +kernel))

def profile19_node35_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 3 36 40 25 38), lower := (rows 1 3 36 40 25 32), losses := [] }

theorem profile19_node35 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,9] 2 profile19_node35_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,9] 2 profile19_node35_cert).mp (by decide +kernel))

def profile19_node36_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 36 40 26 37), lower := (rows 1 3 36 40 26 32), losses := [{ target := 5, region := (rows 63 63 4 8 24 0), good := (rows 3 3 7 27 27 3) }] }

theorem profile19_node36 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,10] 2 profile19_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,10] 2 profile19_node36_cert).mp (by decide +kernel))

def profile19_node37_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 3 36 40 28 35), lower := (rows 1 3 36 40 28 32), losses := [{ target := 0, region := (rows 0 2 44 44 60 32), good := (rows 0 2 60 60 28 60) }] }

theorem profile19_node37 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,12] 2 profile19_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32,12] 2 profile19_node37_cert).mp (by decide +kernel))

def profile19_node31_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node31 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile19_node31_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32,32] (choices 2) [3,5,6,9,10,12] profile19_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node32
  · exact profile19_node33
  · exact profile19_node34
  · exact profile19_node35
  · exact profile19_node36
  · exact profile19_node37

def profile19_node18_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node18 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32] 2 (by decide) (choices 1) [1,2,4,32] profile19_node18_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1,32] (choices 1) [1,2,4,32] profile19_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node19
  · exact profile19_node23
  · exact profile19_node27
  · exact profile19_node31

def profile19_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node2 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1] 2 (by decide) (choices 1) [1,2,8,32] profile19_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,1] (choices 1) [1,2,8,32] profile19_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node3
  · exact profile19_node8
  · exact profile19_node13
  · exact profile19_node18

def profile19_node41_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 6 5 40 49 42), lower := (rows 1 6 5 40 49 32), losses := [] }

theorem profile19_node41 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32,33] 2 profile19_node41_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32,33] 2 profile19_node41_cert).mp (by decide +kernel))

def profile19_node42_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 6 5 40 50 41), lower := (rows 1 6 5 40 50 32), losses := [] }

theorem profile19_node42 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32,34] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32,34] 2 profile19_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32,34] 2 profile19_node42_cert).mp (by decide +kernel))

def profile19_node43_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 6 5 40 56 35), lower := (rows 1 6 5 40 56 32), losses := [] }

theorem profile19_node43 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32,40] 2 profile19_node43_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32,40] 2 profile19_node43_cert).mp (by decide +kernel))

def profile19_node40_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node40 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32] 2 (by decide) (choices 2) [33,34,40] profile19_node40_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1,32] (choices 2) [33,34,40] profile19_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node41
  · exact profile19_node42
  · exact profile19_node43

def profile19_node39_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node39 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1] 2 (by decide) (choices 1) [32] profile19_node39_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,1] (choices 1) [32] profile19_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node40

def profile19_node46_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 6 6 40 49 41), lower := (rows 1 6 6 40 49 32), losses := [] }

theorem profile19_node46 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,2,32,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,2,32,33] 2 profile19_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,2,32,33] 2 profile19_node46_cert).mp (by decide +kernel))

def profile19_node45_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node45 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,2,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,2,32] 2 (by decide) (choices 2) [33] profile19_node45_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,2,32] (choices 2) [33] profile19_node45_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node46

def profile19_node44_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node44 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,2] 2 (by decide) (choices 1) [32] profile19_node44_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,2] (choices 1) [32] profile19_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node45

def profile19_node49_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 6 12 40 49 35), lower := (rows 1 6 12 40 49 32), losses := [] }

theorem profile19_node49 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,8,32,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,8,32,33] 2 profile19_node49_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,8,32,33] 2 profile19_node49_cert).mp (by decide +kernel))

def profile19_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node48 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,8,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,8,32] 2 (by decide) (choices 2) [33] profile19_node48_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,8,32] (choices 2) [33] profile19_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node49

def profile19_node47_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node47 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,8] 2 (by decide) (choices 1) [32] profile19_node47_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,8] (choices 1) [32] profile19_node47_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node48

def profile19_node52_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 6 36 9 49 42), lower := (rows 1 6 36 9 49 32), losses := [] }

theorem profile19_node52 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1,33] 2 profile19_node52_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1,33] 2 profile19_node52_cert).mp (by decide +kernel))

def profile19_node53_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 6 36 9 50 41), lower := (rows 1 6 36 9 50 32), losses := [] }

theorem profile19_node53 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1,34] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1,34] 2 profile19_node53_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1,34] 2 profile19_node53_cert).mp (by decide +kernel))

def profile19_node54_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 6 36 9 56 35), lower := (rows 1 6 36 9 56 32), losses := [] }

theorem profile19_node54 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1,40] 2 profile19_node54_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1,40] 2 profile19_node54_cert).mp (by decide +kernel))

def profile19_node51_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node51 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1] 2 (by decide) (choices 2) [33,34,40] profile19_node51_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,1] (choices 2) [33,34,40] profile19_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node52
  · exact profile19_node53
  · exact profile19_node54

def profile19_node56_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 6 36 10 49 41), lower := (rows 1 6 36 10 49 32), losses := [] }

theorem profile19_node56 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,2,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,2,33] 2 profile19_node56_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,2,33] 2 profile19_node56_cert).mp (by decide +kernel))

def profile19_node55_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node55 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,2] 2 (by decide) (choices 2) [33] profile19_node55_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,2] (choices 2) [33] profile19_node55_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node56

def profile19_node58_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 6 36 40 19 41), lower := (rows 1 6 36 40 19 32), losses := [] }

theorem profile19_node58 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,32,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,32,3] 2 profile19_node58_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,32,3] 2 profile19_node58_cert).mp (by decide +kernel))

def profile19_node59_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 6 36 40 25 35), lower := (rows 1 6 36 40 25 32), losses := [] }

theorem profile19_node59 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,32,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,32,9] 2 profile19_node59_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,32,9] 2 profile19_node59_cert).mp (by decide +kernel))

def profile19_node57_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node57 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,32] 2 (by decide) (choices 2) [3,9] profile19_node57_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32,32] (choices 2) [3,9] profile19_node57_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile19_node58
  · exact profile19_node59

def profile19_node50_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node50 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32] 2 (by decide) (choices 1) [1,2,32] profile19_node50_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4,32] (choices 1) [1,2,32] profile19_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node51
  · exact profile19_node55
  · exact profile19_node57

def profile19_node38_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node38 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4] 2 (by decide) (choices 1) [1,2,8,32] profile19_node38_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,4] (choices 1) [1,2,8,32] profile19_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node39
  · exact profile19_node44
  · exact profile19_node47
  · exact profile19_node50

def profile19_node63_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 5 9 50 44), lower := (rows 1 34 5 9 50 32), losses := [] }

theorem profile19_node63 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1,34] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1,34] 2 profile19_node63_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1,34] 2 profile19_node63_cert).mp (by decide +kernel))

def profile19_node64_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 5 9 52 42), lower := (rows 1 34 5 9 52 32), losses := [] }

theorem profile19_node64 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1,36] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1,36] 2 profile19_node64_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1,36] 2 profile19_node64_cert).mp (by decide +kernel))

def profile19_node65_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 5 9 56 38), lower := (rows 1 34 5 9 56 32), losses := [] }

theorem profile19_node65 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1,40] 2 profile19_node65_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1,40] 2 profile19_node65_cert).mp (by decide +kernel))

def profile19_node62_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node62 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1] 2 (by decide) (choices 2) [34,36,40] profile19_node62_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,1] (choices 2) [34,36,40] profile19_node62_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node63
  · exact profile19_node64
  · exact profile19_node65

def profile19_node67_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 34 5 10 49 44), lower := (rows 1 34 5 10 49 32), losses := [] }

theorem profile19_node67 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2,33] 2 profile19_node67_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2,33] 2 profile19_node67_cert).mp (by decide +kernel))

def profile19_node68_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 5 10 52 41), lower := (rows 1 34 5 10 52 32), losses := [] }

theorem profile19_node68 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2,36] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2,36] 2 profile19_node68_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2,36] 2 profile19_node68_cert).mp (by decide +kernel))

def profile19_node69_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 5 10 56 37), lower := (rows 1 34 5 10 56 32), losses := [] }

theorem profile19_node69 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2,40] 2 profile19_node69_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2,40] 2 profile19_node69_cert).mp (by decide +kernel))

def profile19_node66_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node66 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2] 2 (by decide) (choices 2) [33,36,40] profile19_node66_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,2] (choices 2) [33,36,40] profile19_node66_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node67
  · exact profile19_node68
  · exact profile19_node69

def profile19_node71_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 34 5 12 49 42), lower := (rows 1 34 5 12 49 32), losses := [] }

theorem profile19_node71 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4,33] 2 profile19_node71_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4,33] 2 profile19_node71_cert).mp (by decide +kernel))

def profile19_node72_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 5 12 50 41), lower := (rows 1 34 5 12 50 32), losses := [] }

theorem profile19_node72 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4,34] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4,34] 2 profile19_node72_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4,34] 2 profile19_node72_cert).mp (by decide +kernel))

def profile19_node73_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 5 12 56 35), lower := (rows 1 34 5 12 56 32), losses := [] }

theorem profile19_node73 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4,40] 2 profile19_node73_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4,40] 2 profile19_node73_cert).mp (by decide +kernel))

def profile19_node70_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node70 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4] 2 (by decide) (choices 2) [33,34,40] profile19_node70_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,4] (choices 2) [33,34,40] profile19_node70_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node71
  · exact profile19_node72
  · exact profile19_node73

def profile19_node75_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 5 40 19 44), lower := (rows 1 34 5 40 19 32), losses := [] }

theorem profile19_node75 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,3] 2 profile19_node75_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,3] 2 profile19_node75_cert).mp (by decide +kernel))

def profile19_node76_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 5 40 21 42), lower := (rows 1 34 5 40 21 32), losses := [] }

theorem profile19_node76 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,5] 2 profile19_node76_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,5] 2 profile19_node76_cert).mp (by decide +kernel))

def profile19_node77_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 5 40 22 41), lower := (rows 1 34 5 40 22 32), losses := [{ target := 5, region := (rows 63 2 63 8 18 0), good := (rows 5 23 5 13 23 5) }] }

theorem profile19_node77 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,6] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,6] 2 profile19_node77_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,6] 2 profile19_node77_cert).mp (by decide +kernel))

def profile19_node78_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 5 40 25 38), lower := (rows 1 34 5 40 25 32), losses := [] }

theorem profile19_node78 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,9] 2 profile19_node78_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,9] 2 profile19_node78_cert).mp (by decide +kernel))

def profile19_node79_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 5 40 26 37), lower := (rows 1 34 5 40 26 32), losses := [{ target := 0, region := (rows 0 42 4 42 58 32), good := (rows 0 58 4 58 26 58) }] }

theorem profile19_node79 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,10] 2 profile19_node79_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,10] 2 profile19_node79_cert).mp (by decide +kernel))

def profile19_node80_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 5 40 28 35), lower := (rows 1 34 5 40 28 32), losses := [{ target := 5, region := (rows 63 2 63 8 24 0), good := (rows 5 7 5 29 29 5) }] }

theorem profile19_node80 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,12] 2 profile19_node80_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32,12] 2 profile19_node80_cert).mp (by decide +kernel))

def profile19_node74_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node74 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile19_node74_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1,32] (choices 2) [3,5,6,9,10,12] profile19_node74_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node75
  · exact profile19_node76
  · exact profile19_node77
  · exact profile19_node78
  · exact profile19_node79
  · exact profile19_node80

def profile19_node61_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node61 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1] 2 (by decide) (choices 1) [1,2,4,32] profile19_node61_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,1] (choices 1) [1,2,4,32] profile19_node61_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node62
  · exact profile19_node66
  · exact profile19_node70
  · exact profile19_node74

def profile19_node83_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 34 6 9 49 44), lower := (rows 1 34 6 9 49 32), losses := [] }

theorem profile19_node83 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1,33] 2 profile19_node83_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1,33] 2 profile19_node83_cert).mp (by decide +kernel))

def profile19_node84_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 6 9 52 41), lower := (rows 1 34 6 9 52 32), losses := [] }

theorem profile19_node84 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1,36] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1,36] 2 profile19_node84_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1,36] 2 profile19_node84_cert).mp (by decide +kernel))

def profile19_node85_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 6 9 56 37), lower := (rows 1 34 6 9 56 32), losses := [] }

theorem profile19_node85 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1,40] 2 profile19_node85_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1,40] 2 profile19_node85_cert).mp (by decide +kernel))

def profile19_node82_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node82 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1] 2 (by decide) (choices 2) [33,36,40] profile19_node82_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,1] (choices 2) [33,36,40] profile19_node82_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node83
  · exact profile19_node84
  · exact profile19_node85

def profile19_node87_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 34 6 12 49 41), lower := (rows 1 34 6 12 49 32), losses := [] }

theorem profile19_node87 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,4,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,4,33] 2 profile19_node87_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,4,33] 2 profile19_node87_cert).mp (by decide +kernel))

def profile19_node86_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node86 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,4] 2 (by decide) (choices 2) [33] profile19_node86_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,4] (choices 2) [33] profile19_node86_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node87

def profile19_node89_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 6 40 21 41), lower := (rows 1 34 6 40 21 32), losses := [] }

theorem profile19_node89 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,32,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,32,5] 2 profile19_node89_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,32,5] 2 profile19_node89_cert).mp (by decide +kernel))

def profile19_node90_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 6 40 25 37), lower := (rows 1 34 6 40 25 32), losses := [] }

theorem profile19_node90 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,32,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,32,9] 2 profile19_node90_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,32,9] 2 profile19_node90_cert).mp (by decide +kernel))

def profile19_node88_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node88 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,32] 2 (by decide) (choices 2) [5,9] profile19_node88_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2,32] (choices 2) [5,9] profile19_node88_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile19_node89
  · exact profile19_node90

def profile19_node81_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node81 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2] 2 (by decide) (choices 1) [1,4,32] profile19_node81_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,2] (choices 1) [1,4,32] profile19_node81_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node82
  · exact profile19_node86
  · exact profile19_node88

def profile19_node93_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 34 12 9 49 38), lower := (rows 1 34 12 9 49 32), losses := [] }

theorem profile19_node93 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1,33] 2 profile19_node93_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1,33] 2 profile19_node93_cert).mp (by decide +kernel))

def profile19_node94_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 12 9 50 37), lower := (rows 1 34 12 9 50 32), losses := [] }

theorem profile19_node94 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1,34] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1,34] 2 profile19_node94_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1,34] 2 profile19_node94_cert).mp (by decide +kernel))

def profile19_node95_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 12 9 52 35), lower := (rows 1 34 12 9 52 32), losses := [] }

theorem profile19_node95 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1,36] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1,36] 2 profile19_node95_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1,36] 2 profile19_node95_cert).mp (by decide +kernel))

def profile19_node92_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node92 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1] 2 (by decide) (choices 2) [33,34,36] profile19_node92_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,1] (choices 2) [33,34,36] profile19_node92_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node93
  · exact profile19_node94
  · exact profile19_node95

def profile19_node97_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 34 12 10 49 37), lower := (rows 1 34 12 10 49 32), losses := [] }

theorem profile19_node97 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,2,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,2,33] 2 profile19_node97_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,2,33] 2 profile19_node97_cert).mp (by decide +kernel))

def profile19_node96_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node96 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,2] 2 (by decide) (choices 2) [33] profile19_node96_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,2] (choices 2) [33] profile19_node96_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node97

def profile19_node99_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 34 12 12 49 35), lower := (rows 1 34 12 12 49 32), losses := [] }

theorem profile19_node99 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,4,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,4,33] 2 profile19_node99_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,4,33] 2 profile19_node99_cert).mp (by decide +kernel))

def profile19_node98_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node98 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,4] 2 (by decide) (choices 2) [33] profile19_node98_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,4] (choices 2) [33] profile19_node98_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node99

def profile19_node101_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 12 40 19 37), lower := (rows 1 34 12 40 19 32), losses := [] }

theorem profile19_node101 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,32,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,32,3] 2 profile19_node101_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,32,3] 2 profile19_node101_cert).mp (by decide +kernel))

def profile19_node102_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 12 40 21 35), lower := (rows 1 34 12 40 21 32), losses := [] }

theorem profile19_node102 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,32,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,32,5] 2 profile19_node102_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,32,5] 2 profile19_node102_cert).mp (by decide +kernel))

def profile19_node100_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node100 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,32] 2 (by decide) (choices 2) [3,5] profile19_node100_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8,32] (choices 2) [3,5] profile19_node100_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile19_node101
  · exact profile19_node102

def profile19_node91_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node91 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8] 2 (by decide) (choices 1) [1,2,4,32] profile19_node91_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,8] (choices 1) [1,2,4,32] profile19_node91_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node92
  · exact profile19_node96
  · exact profile19_node98
  · exact profile19_node100

def profile19_node105_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 36 9 19 44), lower := (rows 1 34 36 9 19 32), losses := [] }

theorem profile19_node105 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,3] 2 profile19_node105_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,3] 2 profile19_node105_cert).mp (by decide +kernel))

def profile19_node106_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 36 9 21 42), lower := (rows 1 34 36 9 21 32), losses := [] }

theorem profile19_node106 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,5] 2 profile19_node106_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,5] 2 profile19_node106_cert).mp (by decide +kernel))

def profile19_node107_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 36 9 22 41), lower := (rows 1 34 36 9 22 32), losses := [{ target := 0, region := (rows 0 38 38 8 54 32), good := (rows 0 54 54 8 22 54) }] }

theorem profile19_node107 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,6] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,6] 2 profile19_node107_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,6] 2 profile19_node107_cert).mp (by decide +kernel))

def profile19_node108_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 36 9 25 38), lower := (rows 1 34 36 9 25 32), losses := [] }

theorem profile19_node108 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,9] 2 profile19_node108_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,9] 2 profile19_node108_cert).mp (by decide +kernel))

def profile19_node109_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 36 9 26 37), lower := (rows 1 34 36 9 26 32), losses := [{ target := 5, region := (rows 63 2 4 63 18 0), good := (rows 9 27 13 9 27 9) }] }

theorem profile19_node109 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,10] 2 profile19_node109_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,10] 2 profile19_node109_cert).mp (by decide +kernel))

def profile19_node110_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 36 9 28 35), lower := (rows 1 34 36 9 28 32), losses := [{ target := 5, region := (rows 63 2 4 63 20 0), good := (rows 9 11 29 9 29 9) }] }

theorem profile19_node110 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,12] 2 profile19_node110_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1,12] 2 profile19_node110_cert).mp (by decide +kernel))

def profile19_node104_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node104 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile19_node104_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,1] (choices 2) [3,5,6,9,10,12] profile19_node104_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node105
  · exact profile19_node106
  · exact profile19_node107
  · exact profile19_node108
  · exact profile19_node109
  · exact profile19_node110

def profile19_node112_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 36 10 21 41), lower := (rows 1 34 36 10 21 32), losses := [] }

theorem profile19_node112 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,2,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,2,5] 2 profile19_node112_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,2,5] 2 profile19_node112_cert).mp (by decide +kernel))

def profile19_node113_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 36 10 25 37), lower := (rows 1 34 36 10 25 32), losses := [] }

theorem profile19_node113 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,2,9] 2 profile19_node113_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,2,9] 2 profile19_node113_cert).mp (by decide +kernel))

def profile19_node111_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node111 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,2] 2 (by decide) (choices 2) [5,9] profile19_node111_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,2] (choices 2) [5,9] profile19_node111_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile19_node112
  · exact profile19_node113

def profile19_node115_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 36 12 19 41), lower := (rows 1 34 36 12 19 32), losses := [] }

theorem profile19_node115 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,4,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,4,3] 2 profile19_node115_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,4,3] 2 profile19_node115_cert).mp (by decide +kernel))

def profile19_node116_cert : Bound 6 := { allowed := (rows 0 0 0 0 32 1), upper := (rows 1 34 36 12 25 35), lower := (rows 1 34 36 12 25 32), losses := [] }

theorem profile19_node116 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,4,9] 2 profile19_node116_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,4,9] 2 profile19_node116_cert).mp (by decide +kernel))

def profile19_node114_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node114 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,4] 2 (by decide) (choices 2) [3,9] profile19_node114_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32,4] (choices 2) [3,9] profile19_node114_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile19_node115
  · exact profile19_node116

def profile19_node103_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node103 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32] 2 (by decide) (choices 1) [1,2,4] profile19_node103_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32,32] (choices 1) [1,2,4] profile19_node103_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node104
  · exact profile19_node111
  · exact profile19_node114

def profile19_node60_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node60 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32] 2 (by decide) (choices 1) [1,2,8,32] profile19_node60_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0,32] (choices 1) [1,2,8,32] profile19_node60_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node61
  · exact profile19_node81
  · exact profile19_node91
  · exact profile19_node103

def profile19_node1_route : Route 6 := (fun mask => match mask with | 8 => (4,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile19_node1 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0] 2 (by decide) (choices 1) [1,4,32] profile19_node1_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [0] (choices 1) [1,4,32] profile19_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node2
  · exact profile19_node38
  · exact profile19_node60

def profile19_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile19_node0 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [] 2 (by decide) (choices 0) [0] profile19_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [] (choices 0) [0] profile19_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node1

theorem profile19 : Upper (D (n:=6) [2,9,9,9,16,18]) (R (n:=6) [2,9,9,9,16,18]) [] 2 := profile19_node0

def profile20_node0_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 63 63 63 63 63 63), lower := (rows 1 2 4 8 16 32), losses := [] }

theorem profile20_node0 : Upper (D (n:=6) [2,9,9,9,17,17]) (R (n:=6) [2,9,9,9,17,17]) [] 2 :=
  bound_sound (D (n:=6) [2,9,9,9,17,17]) (R (n:=6) [2,9,9,9,17,17]) [] 2 profile20_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,9,17,17]) (R (n:=6) [2,9,9,9,17,17]) [] 2 profile20_node0_cert).mp (by decide +kernel))

theorem profile20 : Upper (D (n:=6) [2,9,9,9,17,17]) (R (n:=6) [2,9,9,9,17,17]) [] 2 := profile20_node0

def profile21_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 5 10 56 44), lower := (rows 1 3 5 10 56 44), losses := [] }

theorem profile21_node6 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,2,40,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,2,40,12] 2 profile21_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,2,40,12] 2 profile21_node6_cert).mp (by decide +kernel))

def profile21_node5_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node5 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,2,40] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,2,40] 2 (by decide) (choices 2) [12] profile21_node5_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,2,40] (choices 2) [12] profile21_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node6

def profile21_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node4 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,2] 2 (by decide) (choices 2) [40] profile21_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,2] (choices 2) [40] profile21_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node5

def profile21_node9_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 5 12 56 42), lower := (rows 1 3 5 12 56 42), losses := [] }

theorem profile21_node9 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,4,40,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,4,40,10] 2 profile21_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,4,40,10] 2 profile21_node9_cert).mp (by decide +kernel))

def profile21_node8_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node8 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,4,40] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,4,40] 2 (by decide) (choices 2) [10] profile21_node8_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,4,40] (choices 2) [10] profile21_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node9

def profile21_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node7 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,4] 2 (by decide) (choices 2) [40] profile21_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,4] (choices 2) [40] profile21_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node8

def profile21_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 8), upper := (rows 1 3 5 40 26 44), lower := (rows 1 3 5 40 26 32), losses := [{ target := 0, region := (rows 0 2 4 44 16 36), good := (rows 0 2 44 40 26 40) }] }

theorem profile21_node11 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,32,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,32,10] 2 profile21_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,32,10] 2 profile21_node11_cert).mp (by decide +kernel))

def profile21_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 8), upper := (rows 1 3 5 40 28 42), lower := (rows 1 3 5 40 28 32), losses := [{ target := 0, region := (rows 0 2 4 42 16 34), good := (rows 0 42 4 40 28 40) }] }

theorem profile21_node12 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,32,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,32,12] 2 profile21_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,32,12] 2 profile21_node12_cert).mp (by decide +kernel))

def profile21_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node10 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,32] 2 (by decide) (choices 2) [10,12] profile21_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1,32] (choices 2) [10,12] profile21_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node11
  · exact profile21_node12

def profile21_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node3 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1] 2 (by decide) (choices 1) [2,4,32] profile21_node3_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,1] (choices 1) [2,4,32] profile21_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node4
  · exact profile21_node7
  · exact profile21_node10

def profile21_node16_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 6 9 56 44), lower := (rows 1 3 6 9 56 44), losses := [] }

theorem profile21_node16 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,1,40,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,1,40,12] 2 profile21_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,1,40,12] 2 profile21_node16_cert).mp (by decide +kernel))

def profile21_node15_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node15 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,1,40] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,1,40] 2 (by decide) (choices 2) [12] profile21_node15_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,1,40] (choices 2) [12] profile21_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node16

def profile21_node14_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node14 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,1] 2 (by decide) (choices 2) [40] profile21_node14_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,1] (choices 2) [40] profile21_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node15

def profile21_node19_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 3 6 12 56 41), lower := (rows 1 3 6 12 56 41), losses := [] }

theorem profile21_node19 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,4,40,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,4,40,9] 2 profile21_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,4,40,9] 2 profile21_node19_cert).mp (by decide +kernel))

def profile21_node18_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node18 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,4,40] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,4,40] 2 (by decide) (choices 2) [9] profile21_node18_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,4,40] (choices 2) [9] profile21_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node19

def profile21_node17_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node17 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,4] 2 (by decide) (choices 2) [40] profile21_node17_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,4] (choices 2) [40] profile21_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node18

def profile21_node21_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 6 40 25 44), lower := (rows 1 3 6 40 25 32), losses := [] }

theorem profile21_node21 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32,9] 2 profile21_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32,9] 2 profile21_node21_cert).mp (by decide +kernel))

def profile21_node23_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 3 6 40 28 41), lower := (rows 1 3 6 40 28 41), losses := [] }

theorem profile21_node23 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32,12,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32,12,9] 2 profile21_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32,12,9] 2 profile21_node23_cert).mp (by decide +kernel))

def profile21_node22_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node22 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32,12] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32,12] 2 (by decide) (choices 2) [9] profile21_node22_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32,12] (choices 2) [9] profile21_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node23

def profile21_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node20 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32] 2 (by decide) (choices 2) [9,12] profile21_node20_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2,32] (choices 2) [9,12] profile21_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node21
  · exact profile21_node22

def profile21_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node13 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2] 2 (by decide) (choices 1) [1,4,32] profile21_node13_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,2] (choices 1) [1,4,32] profile21_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node14
  · exact profile21_node17
  · exact profile21_node20

def profile21_node26_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 8), upper := (rows 1 3 12 9 50 44), lower := (rows 1 3 12 9 50 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 44), good := (rows 0 2 44 44 50 32) },{ target := 3, region := (rows 63 63 4 0 48 32), good := (rows 3 3 7 3 51 51) }] }

theorem profile21_node26 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,34] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,34] 2 profile21_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,34] 2 profile21_node26_cert).mp (by decide +kernel))

def profile21_node28_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 1), upper := (rows 1 3 12 9 52 42), lower := (rows 1 3 12 9 52 42), losses := [{ target := 0, region := (rows 0 2 44 8 48 32), good := (rows 0 2 12 12 52 62) }] }

theorem profile21_node28 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,36,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,36,10] 2 profile21_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,36,10] 2 profile21_node28_cert).mp (by decide +kernel))

def profile21_node27_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node27 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,36] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,36] 2 (by decide) (choices 2) [10] profile21_node27_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,36] (choices 2) [10] profile21_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node28

def profile21_node29_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 12 9 56 38), lower := (rows 1 3 12 9 56 32), losses := [{ target := 3, region := (rows 63 63 4 0 16 36), good := (rows 3 3 39 3 51 35) }] }

theorem profile21_node29 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,40] 2 profile21_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1,40] 2 profile21_node29_cert).mp (by decide +kernel))

def profile21_node25_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node25 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1] 2 (by decide) (choices 2) [34,36,40] profile21_node25_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,1] (choices 2) [34,36,40] profile21_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node26
  · exact profile21_node27
  · exact profile21_node29

def profile21_node31_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 3 12 10 49 44), lower := (rows 1 3 12 10 49 32), losses := [{ target := 0, region := (rows 0 2 14 10 16 46), good := (rows 0 46 44 46 48 32) }] }

theorem profile21_node31 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,33] 2 profile21_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,33] 2 profile21_node31_cert).mp (by decide +kernel))

def profile21_node33_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 3 12 10 52 41), lower := (rows 1 3 12 10 52 41), losses := [] }

theorem profile21_node33 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,36,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,36,9] 2 profile21_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,36,9] 2 profile21_node33_cert).mp (by decide +kernel))

def profile21_node32_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node32 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,36] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,36] 2 (by decide) (choices 2) [9] profile21_node32_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,36] (choices 2) [9] profile21_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node33

def profile21_node34_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 12 10 56 37), lower := (rows 1 3 12 10 56 32), losses := [{ target := 3, region := (rows 63 63 4 0 16 36), good := (rows 3 3 39 3 51 35) }] }

theorem profile21_node34 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,40] 2 profile21_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2,40] 2 profile21_node34_cert).mp (by decide +kernel))

def profile21_node30_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node30 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2] 2 (by decide) (choices 2) [33,36,40] profile21_node30_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,2] (choices 2) [33,36,40] profile21_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node31
  · exact profile21_node32
  · exact profile21_node34

def profile21_node36_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 3 12 12 49 42), lower := (rows 1 3 12 12 49 32), losses := [{ target := 0, region := (rows 0 2 63 63 16 34), good := (rows 12 46 12 12 60 44) }] }

theorem profile21_node36 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,33] 2 profile21_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,33] 2 profile21_node36_cert).mp (by decide +kernel))

def profile21_node38_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 3 12 12 50 41), lower := (rows 1 3 12 12 50 41), losses := [] }

theorem profile21_node38 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,34,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,34,9] 2 profile21_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,34,9] 2 profile21_node38_cert).mp (by decide +kernel))

def profile21_node37_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node37 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,34] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,34] 2 (by decide) (choices 2) [9] profile21_node37_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,34] (choices 2) [9] profile21_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node38

def profile21_node39_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 12 56 35), lower := (rows 1 3 12 12 56 32), losses := [{ target := 0, region := (rows 0 2 63 63 48 32), good := (rows 12 14 12 12 60 60) }] }

theorem profile21_node39 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,40] 2 profile21_node39_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4,40] 2 profile21_node39_cert).mp (by decide +kernel))

def profile21_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node35 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4] 2 (by decide) (choices 2) [33,34,40] profile21_node35_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,4] (choices 2) [33,34,40] profile21_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node36
  · exact profile21_node37
  · exact profile21_node39

def profile21_node41_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 3 12 40 19 44), lower := (rows 1 3 12 40 19 32), losses := [{ target := 0, region := (rows 0 2 63 63 16 63), good := (rows 44 46 44 44 62 44) }] }

theorem profile21_node41 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,3] 2 profile21_node41_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,3] 2 profile21_node41_cert).mp (by decide +kernel))

def profile21_node42_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 3 12 40 21 42), lower := (rows 1 3 12 40 21 32), losses := [{ target := 0, region := (rows 0 2 46 42 16 34), good := (rows 0 46 12 44 20 44) }] }

theorem profile21_node42 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,5] 2 profile21_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,5] 2 profile21_node42_cert).mp (by decide +kernel))

def profile21_node44_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 3 12 40 22 41), lower := (rows 1 3 12 40 22 41), losses := [] }

theorem profile21_node44 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,6,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,6,9] 2 profile21_node44_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,6,9] 2 profile21_node44_cert).mp (by decide +kernel))

def profile21_node43_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node43 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,6] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,6] 2 (by decide) (choices 2) [9] profile21_node43_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,6] (choices 2) [9] profile21_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node44

def profile21_node45_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 40 25 38), lower := (rows 1 3 12 40 25 32), losses := [] }

theorem profile21_node45 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,9] 2 profile21_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,9] 2 profile21_node45_cert).mp (by decide +kernel))

def profile21_node46_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 12 40 26 37), lower := (rows 1 3 12 40 26 32), losses := [{ target := 3, region := (rows 63 63 4 0 16 36), good := (rows 3 3 39 35 19 35) }] }

theorem profile21_node46 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,10] 2 profile21_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,10] 2 profile21_node46_cert).mp (by decide +kernel))

def profile21_node47_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 40 28 35), lower := (rows 1 3 12 40 28 32), losses := [{ target := 0, region := (rows 0 2 60 40 60 32), good := (rows 0 2 28 60 28 60) }] }

theorem profile21_node47 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,12] 2 profile21_node47_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32,12] 2 profile21_node47_cert).mp (by decide +kernel))

def profile21_node40_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node40 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile21_node40_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8,32] (choices 2) [3,5,6,9,10,12] profile21_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node41
  · exact profile21_node42
  · exact profile21_node43
  · exact profile21_node45
  · exact profile21_node46
  · exact profile21_node47

def profile21_node24_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node24 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8] 2 (by decide) (choices 1) [1,2,4,32] profile21_node24_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,8] (choices 1) [1,2,4,32] profile21_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node25
  · exact profile21_node30
  · exact profile21_node35
  · exact profile21_node40

def profile21_node50_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 8), upper := (rows 1 3 36 9 26 44), lower := (rows 1 3 36 9 26 32), losses := [{ target := 0, region := (rows 0 2 60 8 16 56), good := (rows 0 2 36 44 62 36) }] }

theorem profile21_node50 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1,10] 2 profile21_node50_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1,10] 2 profile21_node50_cert).mp (by decide +kernel))

def profile21_node52_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 36 9 28 42), lower := (rows 1 3 36 9 28 42), losses := [] }

theorem profile21_node52 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1,12,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1,12,10] 2 profile21_node52_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1,12,10] 2 profile21_node52_cert).mp (by decide +kernel))

def profile21_node51_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node51 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1,12] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1,12] 2 (by decide) (choices 2) [10] profile21_node51_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1,12] (choices 2) [10] profile21_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node52

def profile21_node49_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node49 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1] 2 (by decide) (choices 2) [10,12] profile21_node49_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,1] (choices 2) [10,12] profile21_node49_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node50
  · exact profile21_node51

def profile21_node54_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 36 10 25 44), lower := (rows 1 3 36 10 25 32), losses := [] }

theorem profile21_node54 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2,9] 2 profile21_node54_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2,9] 2 profile21_node54_cert).mp (by decide +kernel))

def profile21_node56_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 3 36 10 28 41), lower := (rows 1 3 36 10 28 41), losses := [] }

theorem profile21_node56 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2,12,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2,12,9] 2 profile21_node56_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2,12,9] 2 profile21_node56_cert).mp (by decide +kernel))

def profile21_node55_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node55 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2,12] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2,12] 2 (by decide) (choices 2) [9] profile21_node55_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2,12] (choices 2) [9] profile21_node55_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node56

def profile21_node53_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node53 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2] 2 (by decide) (choices 2) [9,12] profile21_node53_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,2] (choices 2) [9,12] profile21_node53_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node54
  · exact profile21_node55

def profile21_node58_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 36 12 25 42), lower := (rows 1 3 36 12 25 32), losses := [] }

theorem profile21_node58 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4,9] 2 profile21_node58_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4,9] 2 profile21_node58_cert).mp (by decide +kernel))

def profile21_node60_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 3 36 12 26 41), lower := (rows 1 3 36 12 26 41), losses := [] }

theorem profile21_node60 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4,10,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4,10,9] 2 profile21_node60_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4,10,9] 2 profile21_node60_cert).mp (by decide +kernel))

def profile21_node59_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node59 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4,10] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4,10] 2 (by decide) (choices 2) [9] profile21_node59_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4,10] (choices 2) [9] profile21_node59_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node60

def profile21_node57_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node57 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4] 2 (by decide) (choices 2) [9,10] profile21_node57_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32,4] (choices 2) [9,10] profile21_node57_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node58
  · exact profile21_node59

def profile21_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node48 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32] 2 (by decide) (choices 1) [1,2,4] profile21_node48_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1,32] (choices 1) [1,2,4] profile21_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node49
  · exact profile21_node53
  · exact profile21_node57

def profile21_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node2 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1] 2 (by decide) (choices 1) [1,2,8,32] profile21_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,1] (choices 1) [1,2,8,32] profile21_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node3
  · exact profile21_node13
  · exact profile21_node24
  · exact profile21_node48

def profile21_node65_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 6 5 9 56 42), lower := (rows 1 6 5 9 56 42), losses := [] }

theorem profile21_node65 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,1,40,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,1,40,10] 2 profile21_node65_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,1,40,10] 2 profile21_node65_cert).mp (by decide +kernel))

def profile21_node64_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node64 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,1,40] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,1,40] 2 (by decide) (choices 2) [10] profile21_node64_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,1,40] (choices 2) [10] profile21_node64_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node65

def profile21_node63_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node63 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,1] 2 (by decide) (choices 2) [40] profile21_node63_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,1] (choices 2) [40] profile21_node63_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node64

def profile21_node68_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 6 5 10 56 41), lower := (rows 1 6 5 10 56 41), losses := [] }

theorem profile21_node68 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,2,40,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,2,40,9] 2 profile21_node68_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,2,40,9] 2 profile21_node68_cert).mp (by decide +kernel))

def profile21_node67_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node67 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,2,40] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,2,40] 2 (by decide) (choices 2) [9] profile21_node67_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,2,40] (choices 2) [9] profile21_node67_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node68

def profile21_node66_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node66 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,2] 2 (by decide) (choices 2) [40] profile21_node66_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,2] (choices 2) [40] profile21_node66_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node67

def profile21_node70_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 5 40 25 42), lower := (rows 1 6 5 40 25 32), losses := [] }

theorem profile21_node70 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32,9] 2 profile21_node70_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32,9] 2 profile21_node70_cert).mp (by decide +kernel))

def profile21_node72_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 6 5 40 26 41), lower := (rows 1 6 5 40 26 41), losses := [] }

theorem profile21_node72 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32,10,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32,10,9] 2 profile21_node72_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32,10,9] 2 profile21_node72_cert).mp (by decide +kernel))

def profile21_node71_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node71 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32,10] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32,10] 2 (by decide) (choices 2) [9] profile21_node71_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32,10] (choices 2) [9] profile21_node71_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node72

def profile21_node69_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node69 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32] 2 (by decide) (choices 2) [9,10] profile21_node69_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1,32] (choices 2) [9,10] profile21_node69_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node70
  · exact profile21_node71

def profile21_node62_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node62 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1] 2 (by decide) (choices 1) [1,2,32] profile21_node62_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,1] (choices 1) [1,2,32] profile21_node62_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node63
  · exact profile21_node66
  · exact profile21_node69

def profile21_node76_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 6 6 9 56 41), lower := (rows 1 6 6 9 56 41), losses := [] }

theorem profile21_node76 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,1,40,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,1,40,9] 2 profile21_node76_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,1,40,9] 2 profile21_node76_cert).mp (by decide +kernel))

def profile21_node75_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node75 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,1,40] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,1,40] 2 (by decide) (choices 2) [9] profile21_node75_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,1,40] (choices 2) [9] profile21_node75_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node76

def profile21_node74_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node74 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,1] 2 (by decide) (choices 2) [40] profile21_node74_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,1] (choices 2) [40] profile21_node74_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node75

def profile21_node78_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 6 40 25 41), lower := (rows 1 6 6 40 25 32), losses := [] }

theorem profile21_node78 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,32,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,32,9] 2 profile21_node78_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,32,9] 2 profile21_node78_cert).mp (by decide +kernel))

def profile21_node77_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node77 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,32] 2 (by decide) (choices 2) [9] profile21_node77_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2,32] (choices 2) [9] profile21_node77_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node78

def profile21_node73_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node73 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2] 2 (by decide) (choices 1) [1,32] profile21_node73_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,2] (choices 1) [1,32] profile21_node73_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node74
  · exact profile21_node77

def profile21_node81_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 6 12 9 49 42), lower := (rows 1 6 12 9 49 32), losses := [{ target := 0, region := (rows 0 14 12 8 16 44), good := (rows 0 38 46 46 48 32) }] }

theorem profile21_node81 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,33] 2 profile21_node81_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,33] 2 profile21_node81_cert).mp (by decide +kernel))

def profile21_node83_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 6 12 9 50 41), lower := (rows 1 6 12 9 50 41), losses := [] }

theorem profile21_node83 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,34,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,34,9] 2 profile21_node83_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,34,9] 2 profile21_node83_cert).mp (by decide +kernel))

def profile21_node82_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node82 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,34] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,34] 2 (by decide) (choices 2) [9] profile21_node82_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,34] (choices 2) [9] profile21_node82_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node83

def profile21_node84_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 6 12 9 56 35), lower := (rows 1 6 12 9 56 32), losses := [{ target := 3, region := (rows 63 6 4 0 16 38), good := (rows 1 39 39 1 49 33) }] }

theorem profile21_node84 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,40] 2 profile21_node84_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1,40] 2 profile21_node84_cert).mp (by decide +kernel))

def profile21_node80_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node80 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1] 2 (by decide) (choices 2) [33,34,40] profile21_node80_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,1] (choices 2) [33,34,40] profile21_node80_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node81
  · exact profile21_node82
  · exact profile21_node84

def profile21_node86_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 10 49 41), lower := (rows 1 6 12 10 49 32), losses := [{ target := 3, region := (rows 63 6 4 0 48 32), good := (rows 1 7 7 3 49 49) }] }

theorem profile21_node86 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,2,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,2,33] 2 profile21_node86_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,2,33] 2 profile21_node86_cert).mp (by decide +kernel))

def profile21_node85_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node85 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,2] 2 (by decide) (choices 2) [33] profile21_node85_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,2] (choices 2) [33] profile21_node85_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node86

def profile21_node88_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 40 19 41), lower := (rows 1 6 12 40 19 32), losses := [{ target := 3, region := (rows 63 6 4 0 22 32), good := (rows 1 23 23 33 19 33) }] }

theorem profile21_node88 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,32,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,32,3] 2 profile21_node88_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,32,3] 2 profile21_node88_cert).mp (by decide +kernel))

def profile21_node89_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 40 25 35), lower := (rows 1 6 12 40 25 32), losses := [] }

theorem profile21_node89 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,32,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,32,9] 2 profile21_node89_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,32,9] 2 profile21_node89_cert).mp (by decide +kernel))

def profile21_node87_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node87 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,32] 2 (by decide) (choices 2) [3,9] profile21_node87_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8,32] (choices 2) [3,9] profile21_node87_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node88
  · exact profile21_node89

def profile21_node79_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node79 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8] 2 (by decide) (choices 1) [1,2,32] profile21_node79_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,8] (choices 1) [1,2,32] profile21_node79_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node80
  · exact profile21_node85
  · exact profile21_node87

def profile21_node92_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 36 9 25 42), lower := (rows 1 6 36 9 25 32), losses := [] }

theorem profile21_node92 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1,9] 2 profile21_node92_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1,9] 2 profile21_node92_cert).mp (by decide +kernel))

def profile21_node94_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 6 36 9 26 41), lower := (rows 1 6 36 9 26 41), losses := [] }

theorem profile21_node94 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1,10,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1,10,9] 2 profile21_node94_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1,10,9] 2 profile21_node94_cert).mp (by decide +kernel))

def profile21_node93_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node93 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1,10] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1,10] 2 (by decide) (choices 2) [9] profile21_node93_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1,10] (choices 2) [9] profile21_node93_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node94

def profile21_node91_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node91 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1] 2 (by decide) (choices 2) [9,10] profile21_node91_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,1] (choices 2) [9,10] profile21_node91_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node92
  · exact profile21_node93

def profile21_node96_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 36 10 25 41), lower := (rows 1 6 36 10 25 32), losses := [] }

theorem profile21_node96 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,2,9] 2 profile21_node96_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,2,9] 2 profile21_node96_cert).mp (by decide +kernel))

def profile21_node95_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node95 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,2] 2 (by decide) (choices 2) [9] profile21_node95_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32,2] (choices 2) [9] profile21_node95_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node96

def profile21_node90_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node90 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32] 2 (by decide) (choices 1) [1,2] profile21_node90_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4,32] (choices 1) [1,2] profile21_node90_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node91
  · exact profile21_node95

def profile21_node61_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node61 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4] 2 (by decide) (choices 1) [1,2,8,32] profile21_node61_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,4] (choices 1) [1,2,8,32] profile21_node61_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node62
  · exact profile21_node73
  · exact profile21_node79
  · exact profile21_node90

def profile21_node101_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 1), upper := (rows 1 10 5 9 50 44), lower := (rows 1 10 5 9 50 44), losses := [{ target := 0, region := (rows 0 42 4 8 48 32), good := (rows 0 10 4 10 50 62) }] }

theorem profile21_node101 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,34,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,34,12] 2 profile21_node101_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,34,12] 2 profile21_node101_cert).mp (by decide +kernel))

def profile21_node100_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node100 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,34] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,34] 2 (by decide) (choices 2) [12] profile21_node100_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,34] (choices 2) [12] profile21_node100_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node101

def profile21_node102_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 8), upper := (rows 1 10 5 9 52 42), lower := (rows 1 10 5 9 52 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 42), good := (rows 0 42 4 42 52 32) },{ target := 3, region := (rows 63 2 63 0 48 32), good := (rows 5 7 5 5 53 53) }] }

theorem profile21_node102 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,36] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,36] 2 profile21_node102_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,36] 2 profile21_node102_cert).mp (by decide +kernel))

def profile21_node103_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 10 5 9 56 38), lower := (rows 1 10 5 9 56 32), losses := [{ target := 3, region := (rows 63 2 63 0 16 34), good := (rows 5 39 5 5 53 37) }] }

theorem profile21_node103 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,40] 2 profile21_node103_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1,40] 2 profile21_node103_cert).mp (by decide +kernel))

def profile21_node99_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node99 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1] 2 (by decide) (choices 2) [34,36,40] profile21_node99_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,1] (choices 2) [34,36,40] profile21_node99_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node100
  · exact profile21_node102
  · exact profile21_node103

def profile21_node105_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 5 10 49 44), lower := (rows 1 10 5 10 49 32), losses := [{ target := 0, region := (rows 0 63 4 63 16 36), good := (rows 10 10 46 10 58 42) }] }

theorem profile21_node105 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,33] 2 profile21_node105_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,33] 2 profile21_node105_cert).mp (by decide +kernel))

def profile21_node107_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 10 5 10 52 41), lower := (rows 1 10 5 10 52 41), losses := [] }

theorem profile21_node107 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,36,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,36,9] 2 profile21_node107_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,36,9] 2 profile21_node107_cert).mp (by decide +kernel))

def profile21_node106_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node106 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,36] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,36] 2 (by decide) (choices 2) [9] profile21_node106_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,36] (choices 2) [9] profile21_node106_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node107

def profile21_node108_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 10 56 37), lower := (rows 1 10 5 10 56 32), losses := [{ target := 0, region := (rows 0 63 4 63 48 32), good := (rows 10 10 14 10 58 58) }] }

theorem profile21_node108 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,40] 2 profile21_node108_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2,40] 2 profile21_node108_cert).mp (by decide +kernel))

def profile21_node104_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node104 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2] 2 (by decide) (choices 2) [33,36,40] profile21_node104_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,2] (choices 2) [33,36,40] profile21_node104_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node105
  · exact profile21_node106
  · exact profile21_node108

def profile21_node110_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 5 12 49 42), lower := (rows 1 10 5 12 49 32), losses := [{ target := 0, region := (rows 0 14 4 12 16 46), good := (rows 0 42 46 46 48 32) }] }

theorem profile21_node110 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,33] 2 profile21_node110_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,33] 2 profile21_node110_cert).mp (by decide +kernel))

def profile21_node112_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 10 5 12 50 41), lower := (rows 1 10 5 12 50 41), losses := [] }

theorem profile21_node112 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,34,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,34,9] 2 profile21_node112_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,34,9] 2 profile21_node112_cert).mp (by decide +kernel))

def profile21_node111_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node111 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,34] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,34] 2 (by decide) (choices 2) [9] profile21_node111_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,34] (choices 2) [9] profile21_node111_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node112

def profile21_node113_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 10 5 12 56 35), lower := (rows 1 10 5 12 56 32), losses := [{ target := 3, region := (rows 63 2 63 0 16 34), good := (rows 5 39 5 5 53 37) }] }

theorem profile21_node113 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,40] 2 profile21_node113_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4,40] 2 profile21_node113_cert).mp (by decide +kernel))

def profile21_node109_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node109 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4] 2 (by decide) (choices 2) [33,34,40] profile21_node109_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,4] (choices 2) [33,34,40] profile21_node109_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node110
  · exact profile21_node111
  · exact profile21_node113

def profile21_node115_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 5 40 19 44), lower := (rows 1 10 5 40 19 32), losses := [{ target := 0, region := (rows 0 46 4 44 16 36), good := (rows 0 10 46 42 18 42) }] }

theorem profile21_node115 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,3] 2 profile21_node115_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,3] 2 profile21_node115_cert).mp (by decide +kernel))

def profile21_node116_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 5 40 21 42), lower := (rows 1 10 5 40 21 32), losses := [{ target := 0, region := (rows 0 63 4 63 16 63), good := (rows 42 42 46 42 62 42) }] }

theorem profile21_node116 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,5] 2 profile21_node116_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,5] 2 profile21_node116_cert).mp (by decide +kernel))

def profile21_node118_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 10 5 40 22 41), lower := (rows 1 10 5 40 22 41), losses := [] }

theorem profile21_node118 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,6,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,6,9] 2 profile21_node118_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,6,9] 2 profile21_node118_cert).mp (by decide +kernel))

def profile21_node117_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node117 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,6] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,6] 2 (by decide) (choices 2) [9] profile21_node117_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,6] (choices 2) [9] profile21_node117_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node118

def profile21_node119_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 40 25 38), lower := (rows 1 10 5 40 25 32), losses := [] }

theorem profile21_node119 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,9] 2 profile21_node119_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,9] 2 profile21_node119_cert).mp (by decide +kernel))

def profile21_node120_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 40 26 37), lower := (rows 1 10 5 40 26 32), losses := [{ target := 0, region := (rows 0 58 4 40 58 32), good := (rows 0 26 4 58 26 58) }] }

theorem profile21_node120 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,10] 2 profile21_node120_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,10] 2 profile21_node120_cert).mp (by decide +kernel))

def profile21_node121_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 10 5 40 28 35), lower := (rows 1 10 5 40 28 32), losses := [{ target := 3, region := (rows 63 2 63 0 16 34), good := (rows 5 39 5 37 21 37) }] }

theorem profile21_node121 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,12] 2 profile21_node121_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32,12] 2 profile21_node121_cert).mp (by decide +kernel))

def profile21_node114_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node114 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile21_node114_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1,32] (choices 2) [3,5,6,9,10,12] profile21_node114_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node115
  · exact profile21_node116
  · exact profile21_node117
  · exact profile21_node119
  · exact profile21_node120
  · exact profile21_node121

def profile21_node98_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node98 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1] 2 (by decide) (choices 1) [1,2,4,32] profile21_node98_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,1] (choices 1) [1,2,4,32] profile21_node98_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node99
  · exact profile21_node104
  · exact profile21_node109
  · exact profile21_node114

def profile21_node124_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 6 9 49 44), lower := (rows 1 10 6 9 49 32), losses := [{ target := 0, region := (rows 0 10 14 8 16 42), good := (rows 0 46 38 46 48 32) }] }

theorem profile21_node124 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,33] 2 profile21_node124_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,33] 2 profile21_node124_cert).mp (by decide +kernel))

def profile21_node126_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 10 6 9 52 41), lower := (rows 1 10 6 9 52 41), losses := [] }

theorem profile21_node126 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,36,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,36,9] 2 profile21_node126_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,36,9] 2 profile21_node126_cert).mp (by decide +kernel))

def profile21_node125_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node125 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,36] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,36] 2 (by decide) (choices 2) [9] profile21_node125_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,36] (choices 2) [9] profile21_node125_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node126

def profile21_node127_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 10 6 9 56 37), lower := (rows 1 10 6 9 56 32), losses := [{ target := 3, region := (rows 63 2 6 0 16 38), good := (rows 1 39 39 1 49 33) }] }

theorem profile21_node127 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,40] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,40] 2 profile21_node127_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1,40] 2 profile21_node127_cert).mp (by decide +kernel))

def profile21_node123_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node123 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1] 2 (by decide) (choices 2) [33,36,40] profile21_node123_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,1] (choices 2) [33,36,40] profile21_node123_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node124
  · exact profile21_node125
  · exact profile21_node127

def profile21_node129_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 6 12 49 41), lower := (rows 1 10 6 12 49 32), losses := [{ target := 3, region := (rows 63 2 6 0 48 32), good := (rows 1 7 7 5 49 49) }] }

theorem profile21_node129 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,4,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,4,33] 2 profile21_node129_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,4,33] 2 profile21_node129_cert).mp (by decide +kernel))

def profile21_node128_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node128 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,4] 2 (by decide) (choices 2) [33] profile21_node128_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,4] (choices 2) [33] profile21_node128_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node129

def profile21_node131_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 6 40 21 41), lower := (rows 1 10 6 40 21 32), losses := [{ target := 3, region := (rows 63 2 6 0 22 32), good := (rows 1 23 23 33 21 33) }] }

theorem profile21_node131 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,32,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,32,5] 2 profile21_node131_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,32,5] 2 profile21_node131_cert).mp (by decide +kernel))

def profile21_node132_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 6 40 25 37), lower := (rows 1 10 6 40 25 32), losses := [] }

theorem profile21_node132 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,32,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,32,9] 2 profile21_node132_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,32,9] 2 profile21_node132_cert).mp (by decide +kernel))

def profile21_node130_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node130 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,32] 2 (by decide) (choices 2) [5,9] profile21_node130_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2,32] (choices 2) [5,9] profile21_node130_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node131
  · exact profile21_node132

def profile21_node122_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node122 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2] 2 (by decide) (choices 1) [1,4,32] profile21_node122_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,2] (choices 1) [1,4,32] profile21_node122_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node123
  · exact profile21_node128
  · exact profile21_node130

def profile21_node135_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 12 9 49 38), lower := (rows 1 10 12 9 49 32), losses := [{ target := 0, region := (rows 0 14 14 8 16 46), good := (rows 0 46 46 46 48 32) }] }

theorem profile21_node135 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,33] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,33] 2 profile21_node135_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,33] 2 profile21_node135_cert).mp (by decide +kernel))

def profile21_node137_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 12 9 50 37), lower := (rows 1 10 12 9 50 37), losses := [{ target := 0, region := (rows 0 14 14 8 48 32), good := (rows 0 14 14 14 54 54) }] }

theorem profile21_node137 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,34,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,34,5] 2 profile21_node137_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,34,5] 2 profile21_node137_cert).mp (by decide +kernel))

def profile21_node136_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node136 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,34] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,34] 2 (by decide) (choices 2) [5] profile21_node136_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,34] (choices 2) [5] profile21_node136_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node137

def profile21_node139_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 12 9 52 35), lower := (rows 1 10 12 9 52 35), losses := [{ target := 0, region := (rows 0 14 14 8 48 32), good := (rows 0 14 14 14 54 54) }] }

theorem profile21_node139 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,36,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,36,3] 2 profile21_node139_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,36,3] 2 profile21_node139_cert).mp (by decide +kernel))

def profile21_node138_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node138 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,36] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,36] 2 (by decide) (choices 2) [3] profile21_node138_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1,36] (choices 2) [3] profile21_node138_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node139

def profile21_node134_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node134 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1] 2 (by decide) (choices 2) [33,34,36] profile21_node134_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,1] (choices 2) [33,34,36] profile21_node134_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node135
  · exact profile21_node136
  · exact profile21_node138

def profile21_node140_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 10 12 10 53 37), lower := (rows 1 10 12 10 16 32), losses := [{ target := 3, region := (rows 63 2 4 0 20 36), good := (rows 1 3 53 3 17 33) }] }

theorem profile21_node140 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,2] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,2] 2 profile21_node140_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,2] 2 profile21_node140_cert).mp (by decide +kernel))

def profile21_node141_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 10 12 12 51 35), lower := (rows 1 10 12 12 16 32), losses := [{ target := 3, region := (rows 63 2 4 0 18 34), good := (rows 1 51 5 5 17 33) }] }

theorem profile21_node141 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,4] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,4] 2 profile21_node141_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,4] 2 profile21_node141_cert).mp (by decide +kernel))

def profile21_node143_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 10 12 40 19 37), lower := (rows 1 10 12 40 19 32), losses := [{ target := 3, region := (rows 63 2 4 0 18 36), good := (rows 1 19 37 33 19 33) }] }

theorem profile21_node143 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,32,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,32,3] 2 profile21_node143_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,32,3] 2 profile21_node143_cert).mp (by decide +kernel))

def profile21_node144_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 10 12 40 21 35), lower := (rows 1 10 12 40 21 32), losses := [{ target := 3, region := (rows 63 2 4 0 20 34), good := (rows 1 35 21 33 21 33) }] }

theorem profile21_node144 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,32,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,32,5] 2 profile21_node144_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,32,5] 2 profile21_node144_cert).mp (by decide +kernel))

def profile21_node142_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node142 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,32] 2 (by decide) (choices 2) [3,5] profile21_node142_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8,32] (choices 2) [3,5] profile21_node142_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node143
  · exact profile21_node144

def profile21_node133_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node133 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8] 2 (by decide) (choices 1) [1,2,4,32] profile21_node133_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,8] (choices 1) [1,2,4,32] profile21_node133_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node134
  · exact profile21_node140
  · exact profile21_node141
  · exact profile21_node142

def profile21_node147_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 36 9 19 44), lower := (rows 1 10 36 9 19 32), losses := [{ target := 0, region := (rows 0 10 62 8 16 42), good := (rows 0 46 36 46 54 36) }] }

theorem profile21_node147 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,3] 2 profile21_node147_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,3] 2 profile21_node147_cert).mp (by decide +kernel))

def profile21_node148_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 36 9 21 42), lower := (rows 1 10 36 9 21 32), losses := [{ target := 0, region := (rows 0 10 46 8 16 42), good := (rows 0 46 36 46 20 36) }] }

theorem profile21_node148 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,5] 2 profile21_node148_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,5] 2 profile21_node148_cert).mp (by decide +kernel))

def profile21_node150_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 10 36 9 22 41), lower := (rows 1 10 36 9 22 41), losses := [] }

theorem profile21_node150 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,6,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,6,9] 2 profile21_node150_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,6,9] 2 profile21_node150_cert).mp (by decide +kernel))

def profile21_node149_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node149 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,6] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,6] 2 (by decide) (choices 2) [9] profile21_node149_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,6] (choices 2) [9] profile21_node149_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node150

def profile21_node151_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 36 9 25 38), lower := (rows 1 10 36 9 25 32), losses := [] }

theorem profile21_node151 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,9] 2 profile21_node151_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,9] 2 profile21_node151_cert).mp (by decide +kernel))

def profile21_node152_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 36 9 26 37), lower := (rows 1 10 36 9 26 32), losses := [{ target := 0, region := (rows 0 26 36 8 26 32), good := (rows 0 26 36 26 26 36) }] }

theorem profile21_node152 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,10] 2 profile21_node152_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,10] 2 profile21_node152_cert).mp (by decide +kernel))

def profile21_node153_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 10 36 9 28 35), lower := (rows 1 10 36 9 28 32), losses := [{ target := 3, region := (rows 63 2 38 0 16 34), good := (rows 1 39 37 1 21 37) }] }

theorem profile21_node153 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,12] 2 profile21_node153_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1,12] 2 profile21_node153_cert).mp (by decide +kernel))

def profile21_node146_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node146 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile21_node146_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,1] (choices 2) [3,5,6,9,10,12] profile21_node146_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node147
  · exact profile21_node148
  · exact profile21_node149
  · exact profile21_node151
  · exact profile21_node152
  · exact profile21_node153

def profile21_node155_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 36 10 21 41), lower := (rows 1 10 36 10 21 32), losses := [{ target := 3, region := (rows 63 2 36 0 52 32), good := (rows 1 3 53 3 21 53) }] }

theorem profile21_node155 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,2,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,2,5] 2 profile21_node155_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,2,5] 2 profile21_node155_cert).mp (by decide +kernel))

def profile21_node156_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 36 10 25 37), lower := (rows 1 10 36 10 25 32), losses := [] }

theorem profile21_node156 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,2,9] 2 profile21_node156_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,2,9] 2 profile21_node156_cert).mp (by decide +kernel))

def profile21_node154_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node154 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,2] 2 (by decide) (choices 2) [5,9] profile21_node154_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,2] (choices 2) [5,9] profile21_node154_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node155
  · exact profile21_node156

def profile21_node158_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 36 12 19 41), lower := (rows 1 10 36 12 19 32), losses := [{ target := 3, region := (rows 63 2 36 0 18 32), good := (rows 1 19 37 5 19 37) }] }

theorem profile21_node158 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,4,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,4,3] 2 profile21_node158_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,4,3] 2 profile21_node158_cert).mp (by decide +kernel))

def profile21_node159_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 36 12 25 35), lower := (rows 1 10 36 12 25 32), losses := [] }

theorem profile21_node159 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,4,9] 2 profile21_node159_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,4,9] 2 profile21_node159_cert).mp (by decide +kernel))

def profile21_node157_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node157 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,4] 2 (by decide) (choices 2) [3,9] profile21_node157_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32,4] (choices 2) [3,9] profile21_node157_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node158
  · exact profile21_node159

def profile21_node145_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node145 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32] 2 (by decide) (choices 1) [1,2,4] profile21_node145_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8,32] (choices 1) [1,2,4] profile21_node145_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node146
  · exact profile21_node154
  · exact profile21_node157

def profile21_node97_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node97 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8] 2 (by decide) (choices 1) [1,2,8,32] profile21_node97_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,8] (choices 1) [1,2,8,32] profile21_node97_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node98
  · exact profile21_node122
  · exact profile21_node133
  · exact profile21_node145

def profile21_node164_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 5 9 26 44), lower := (rows 1 34 5 9 26 44), losses := [] }

theorem profile21_node164 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1,10,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1,10,12] 2 profile21_node164_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1,10,12] 2 profile21_node164_cert).mp (by decide +kernel))

def profile21_node163_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node163 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1,10] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1,10] 2 (by decide) (choices 2) [12] profile21_node163_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1,10] (choices 2) [12] profile21_node163_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node164

def profile21_node165_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 8), upper := (rows 1 34 5 9 28 42), lower := (rows 1 34 5 9 28 32), losses := [{ target := 0, region := (rows 0 58 4 8 16 56), good := (rows 0 34 4 42 62 34) }] }

theorem profile21_node165 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1,12] 2 profile21_node165_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1,12] 2 profile21_node165_cert).mp (by decide +kernel))

def profile21_node162_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node162 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1] 2 (by decide) (choices 2) [10,12] profile21_node162_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,1] (choices 2) [10,12] profile21_node162_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node163
  · exact profile21_node165

def profile21_node167_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 34 5 10 25 44), lower := (rows 1 34 5 10 25 32), losses := [] }

theorem profile21_node167 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2,9] 2 profile21_node167_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2,9] 2 profile21_node167_cert).mp (by decide +kernel))

def profile21_node169_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 34 5 10 28 41), lower := (rows 1 34 5 10 28 41), losses := [] }

theorem profile21_node169 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2,12,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2,12,9] 2 profile21_node169_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2,12,9] 2 profile21_node169_cert).mp (by decide +kernel))

def profile21_node168_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node168 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2,12] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2,12] 2 (by decide) (choices 2) [9] profile21_node168_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2,12] (choices 2) [9] profile21_node168_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node169

def profile21_node166_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node166 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2] 2 (by decide) (choices 2) [9,12] profile21_node166_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,2] (choices 2) [9,12] profile21_node166_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node167
  · exact profile21_node168

def profile21_node171_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 34 5 12 25 42), lower := (rows 1 34 5 12 25 32), losses := [] }

theorem profile21_node171 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4,9] 2 profile21_node171_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4,9] 2 profile21_node171_cert).mp (by decide +kernel))

def profile21_node173_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 34 5 12 26 41), lower := (rows 1 34 5 12 26 41), losses := [] }

theorem profile21_node173 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4,10,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4,10,9] 2 profile21_node173_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4,10,9] 2 profile21_node173_cert).mp (by decide +kernel))

def profile21_node172_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node172 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4,10] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4,10] 2 (by decide) (choices 2) [9] profile21_node172_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4,10] (choices 2) [9] profile21_node172_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node173

def profile21_node170_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node170 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4] 2 (by decide) (choices 2) [9,10] profile21_node170_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1,4] (choices 2) [9,10] profile21_node170_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node171
  · exact profile21_node172

def profile21_node161_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node161 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1] 2 (by decide) (choices 1) [1,2,4] profile21_node161_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,1] (choices 1) [1,2,4] profile21_node161_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node162
  · exact profile21_node166
  · exact profile21_node170

def profile21_node176_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 34 6 9 25 44), lower := (rows 1 34 6 9 25 32), losses := [] }

theorem profile21_node176 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1,9] 2 profile21_node176_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1,9] 2 profile21_node176_cert).mp (by decide +kernel))

def profile21_node178_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 34 6 9 28 41), lower := (rows 1 34 6 9 28 41), losses := [] }

theorem profile21_node178 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1,12,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1,12,9] 2 profile21_node178_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1,12,9] 2 profile21_node178_cert).mp (by decide +kernel))

def profile21_node177_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node177 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1,12] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1,12] 2 (by decide) (choices 2) [9] profile21_node177_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1,12] (choices 2) [9] profile21_node177_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node178

def profile21_node175_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node175 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1] 2 (by decide) (choices 2) [9,12] profile21_node175_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,1] (choices 2) [9,12] profile21_node175_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node176
  · exact profile21_node177

def profile21_node180_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 34 6 12 25 41), lower := (rows 1 34 6 12 25 32), losses := [] }

theorem profile21_node180 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,4,9] 2 profile21_node180_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,4,9] 2 profile21_node180_cert).mp (by decide +kernel))

def profile21_node179_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node179 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,4] 2 (by decide) (choices 2) [9] profile21_node179_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2,4] (choices 2) [9] profile21_node179_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node180

def profile21_node174_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node174 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2] 2 (by decide) (choices 1) [1,4] profile21_node174_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,2] (choices 1) [1,4] profile21_node174_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node175
  · exact profile21_node179

def profile21_node183_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 34 12 9 19 44), lower := (rows 1 34 12 9 19 32), losses := [{ target := 0, region := (rows 0 46 12 8 16 44), good := (rows 0 34 46 46 18 34) }] }

theorem profile21_node183 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,3] 2 profile21_node183_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,3] 2 profile21_node183_cert).mp (by decide +kernel))

def profile21_node184_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 34 12 9 21 42), lower := (rows 1 34 12 9 21 32), losses := [{ target := 0, region := (rows 0 62 12 8 16 44), good := (rows 0 34 46 46 54 34) }] }

theorem profile21_node184 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,5] 2 profile21_node184_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,5] 2 profile21_node184_cert).mp (by decide +kernel))

def profile21_node186_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 34 12 9 22 41), lower := (rows 1 34 12 9 22 41), losses := [] }

theorem profile21_node186 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,6,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,6,9] 2 profile21_node186_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,6,9] 2 profile21_node186_cert).mp (by decide +kernel))

def profile21_node185_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node185 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,6] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,6] 2 (by decide) (choices 2) [9] profile21_node185_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,6] (choices 2) [9] profile21_node185_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node186

def profile21_node187_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 34 12 9 25 38), lower := (rows 1 34 12 9 25 32), losses := [] }

theorem profile21_node187 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,9] 2 profile21_node187_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,9] 2 profile21_node187_cert).mp (by decide +kernel))

def profile21_node188_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 34 12 9 26 37), lower := (rows 1 34 12 9 26 32), losses := [{ target := 3, region := (rows 63 38 4 0 16 36), good := (rows 1 35 39 1 19 35) }] }

theorem profile21_node188 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,10] 2 profile21_node188_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,10] 2 profile21_node188_cert).mp (by decide +kernel))

def profile21_node189_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 34 12 9 28 35), lower := (rows 1 34 12 9 28 32), losses := [{ target := 0, region := (rows 0 34 28 8 28 32), good := (rows 0 34 28 28 28 34) }] }

theorem profile21_node189 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,12] 2 profile21_node189_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1,12] 2 profile21_node189_cert).mp (by decide +kernel))

def profile21_node182_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node182 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile21_node182_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,1] (choices 2) [3,5,6,9,10,12] profile21_node182_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node183
  · exact profile21_node184
  · exact profile21_node185
  · exact profile21_node187
  · exact profile21_node188
  · exact profile21_node189

def profile21_node191_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 34 12 10 21 41), lower := (rows 1 34 12 10 21 32), losses := [{ target := 3, region := (rows 63 34 4 0 20 32), good := (rows 1 35 21 3 21 35) }] }

theorem profile21_node191 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,2,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,2,5] 2 profile21_node191_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,2,5] 2 profile21_node191_cert).mp (by decide +kernel))

def profile21_node192_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 34 12 10 25 37), lower := (rows 1 34 12 10 25 32), losses := [] }

theorem profile21_node192 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,2,9] 2 profile21_node192_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,2,9] 2 profile21_node192_cert).mp (by decide +kernel))

def profile21_node190_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node190 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,2] 2 (by decide) (choices 2) [5,9] profile21_node190_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,2] (choices 2) [5,9] profile21_node190_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node191
  · exact profile21_node192

def profile21_node194_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 34 12 12 19 41), lower := (rows 1 34 12 12 19 32), losses := [{ target := 3, region := (rows 63 34 4 0 50 32), good := (rows 1 51 5 5 19 51) }] }

theorem profile21_node194 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,4,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,4,3] 2 profile21_node194_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,4,3] 2 profile21_node194_cert).mp (by decide +kernel))

def profile21_node195_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 34 12 12 25 35), lower := (rows 1 34 12 12 25 32), losses := [] }

theorem profile21_node195 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,4,9] 2 profile21_node195_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,4,9] 2 profile21_node195_cert).mp (by decide +kernel))

def profile21_node193_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node193 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,4] 2 (by decide) (choices 2) [3,9] profile21_node193_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8,4] (choices 2) [3,9] profile21_node193_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node194
  · exact profile21_node195

def profile21_node181_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node181 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8] 2 (by decide) (choices 1) [1,2,4] profile21_node181_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32,8] (choices 1) [1,2,4] profile21_node181_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node182
  · exact profile21_node190
  · exact profile21_node193

def profile21_node160_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node160 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32] 2 (by decide) (choices 1) [1,2,8] profile21_node160_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0,32] (choices 1) [1,2,8] profile21_node160_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node161
  · exact profile21_node174
  · exact profile21_node181

def profile21_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node1 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0] 2 (by decide) (choices 1) [1,4,8,32] profile21_node1_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [0] (choices 1) [1,4,8,32] profile21_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node2
  · exact profile21_node61
  · exact profile21_node97
  · exact profile21_node160

def profile21_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile21_node0 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [] 2 (by decide) (choices 0) [0] profile21_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [] (choices 0) [0] profile21_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node1

theorem profile21 : Upper (D (n:=6) [2,9,9,10,16,17]) (R (n:=6) [2,9,9,10,16,17]) [] 2 := profile21_node0

def profile22_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 8), upper := (rows 1 3 12 9 26 44), lower := (rows 1 3 12 9 26 32), losses := [{ target := 0, region := (rows 0 2 28 8 16 60), good := (rows 0 2 44 44 62 32) }] }

theorem profile22_node5 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,1,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,1,10] 2 profile22_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,1,10] 2 profile22_node5_cert).mp (by decide +kernel))

def profile22_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 9 28 42), lower := (rows 1 3 12 9 28 32), losses := [{ target := 0, region := (rows 0 2 28 8 28 32), good := (rows 0 2 28 28 28 32) }] }

theorem profile22_node6 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,1,12] 2 profile22_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,1,12] 2 profile22_node6_cert).mp (by decide +kernel))

def profile22_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node4 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,1] 2 (by decide) (choices 2) [10,12] profile22_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,1] (choices 2) [10,12] profile22_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node5
  · exact profile22_node6

def profile22_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 10 25 44), lower := (rows 1 3 12 10 25 32), losses := [] }

theorem profile22_node8 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,2,9] 2 profile22_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,2,9] 2 profile22_node8_cert).mp (by decide +kernel))

def profile22_node9_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 10 28 41), lower := (rows 1 3 12 10 28 32), losses := [{ target := 0, region := (rows 0 2 30 10 30 32), good := (rows 0 30 28 30 28 32) }] }

theorem profile22_node9 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,2,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,2,12] 2 profile22_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,2,12] 2 profile22_node9_cert).mp (by decide +kernel))

def profile22_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node7 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,2] 2 (by decide) (choices 2) [9,12] profile22_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,2] (choices 2) [9,12] profile22_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node8
  · exact profile22_node9

def profile22_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 12 25 42), lower := (rows 1 3 12 12 25 32), losses := [] }

theorem profile22_node11 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,4,9] 2 profile22_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,4,9] 2 profile22_node11_cert).mp (by decide +kernel))

def profile22_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 12 26 41), lower := (rows 1 3 12 12 26 32), losses := [{ target := 0, region := (rows 0 2 63 63 18 32), good := (rows 12 30 12 12 30 44) }] }

theorem profile22_node12 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,4,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,4,10] 2 profile22_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,4,10] 2 profile22_node12_cert).mp (by decide +kernel))

def profile22_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node10 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,4] 2 (by decide) (choices 2) [9,10] profile22_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8,4] (choices 2) [9,10] profile22_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node11
  · exact profile22_node12

def profile22_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node3 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8] 2 (by decide) (choices 1) [1,2,4] profile22_node3_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1,8] (choices 1) [1,2,4] profile22_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile22_node4
  · exact profile22_node7
  · exact profile22_node10

def profile22_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node2 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1] 2 (by decide) (choices 1) [8] profile22_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,1] (choices 1) [8] profile22_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node3

def profile22_node16_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 9 25 42), lower := (rows 1 6 12 9 25 32), losses := [] }

theorem profile22_node16 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,1,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,1,9] 2 profile22_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,1,9] 2 profile22_node16_cert).mp (by decide +kernel))

def profile22_node17_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 9 26 41), lower := (rows 1 6 12 9 26 32), losses := [{ target := 0, region := (rows 0 30 28 8 28 32), good := (rows 0 22 30 30 30 32) }] }

theorem profile22_node17 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,1,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,1,10] 2 profile22_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,1,10] 2 profile22_node17_cert).mp (by decide +kernel))

def profile22_node15_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node15 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,1] 2 (by decide) (choices 2) [9,10] profile22_node15_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,1] (choices 2) [9,10] profile22_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node16
  · exact profile22_node17

def profile22_node19_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 10 25 41), lower := (rows 1 6 12 10 25 32), losses := [] }

theorem profile22_node19 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,2,9] 2 profile22_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,2,9] 2 profile22_node19_cert).mp (by decide +kernel))

def profile22_node18_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node18 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,2] 2 (by decide) (choices 2) [9] profile22_node18_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8,2] (choices 2) [9] profile22_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node19

def profile22_node14_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node14 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8] 2 (by decide) (choices 1) [1,2] profile22_node14_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4,8] (choices 1) [1,2] profile22_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node15
  · exact profile22_node18

def profile22_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node13 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4] 2 (by decide) (choices 1) [8] profile22_node13_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,4] (choices 1) [8] profile22_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node14

def profile22_node23_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 9 26 44), lower := (rows 1 10 5 9 26 32), losses := [{ target := 0, region := (rows 0 26 4 8 26 32), good := (rows 0 26 4 26 26 32) }] }

theorem profile22_node23 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,1,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,1,10] 2 profile22_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,1,10] 2 profile22_node23_cert).mp (by decide +kernel))

def profile22_node24_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 8), upper := (rows 1 10 5 9 28 42), lower := (rows 1 10 5 9 28 32), losses := [{ target := 0, region := (rows 0 26 4 8 16 58), good := (rows 0 42 4 42 62 32) }] }

theorem profile22_node24 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,1,12] 2 profile22_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,1,12] 2 profile22_node24_cert).mp (by decide +kernel))

def profile22_node22_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node22 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,1] 2 (by decide) (choices 2) [10,12] profile22_node22_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,1] (choices 2) [10,12] profile22_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node23
  · exact profile22_node24

def profile22_node26_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 10 25 44), lower := (rows 1 10 5 10 25 32), losses := [] }

theorem profile22_node26 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,2,9] 2 profile22_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,2,9] 2 profile22_node26_cert).mp (by decide +kernel))

def profile22_node27_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 10 28 41), lower := (rows 1 10 5 10 28 32), losses := [{ target := 0, region := (rows 0 63 4 63 20 32), good := (rows 10 10 30 10 30 42) }] }

theorem profile22_node27 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,2,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,2,12] 2 profile22_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,2,12] 2 profile22_node27_cert).mp (by decide +kernel))

def profile22_node25_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node25 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,2] 2 (by decide) (choices 2) [9,12] profile22_node25_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,2] (choices 2) [9,12] profile22_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node26
  · exact profile22_node27

def profile22_node29_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 12 25 42), lower := (rows 1 10 5 12 25 32), losses := [] }

theorem profile22_node29 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,4,9] 2 profile22_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,4,9] 2 profile22_node29_cert).mp (by decide +kernel))

def profile22_node30_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 12 26 41), lower := (rows 1 10 5 12 26 32), losses := [{ target := 0, region := (rows 0 30 4 12 30 32), good := (rows 0 26 30 30 26 32) }] }

theorem profile22_node30 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,4,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,4,10] 2 profile22_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,4,10] 2 profile22_node30_cert).mp (by decide +kernel))

def profile22_node28_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node28 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,4] 2 (by decide) (choices 2) [9,10] profile22_node28_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1,4] (choices 2) [9,10] profile22_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node29
  · exact profile22_node30

def profile22_node21_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node21 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1] 2 (by decide) (choices 1) [1,2,4] profile22_node21_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,1] (choices 1) [1,2,4] profile22_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile22_node22
  · exact profile22_node25
  · exact profile22_node28

def profile22_node33_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 6 9 25 44), lower := (rows 1 10 6 9 25 32), losses := [] }

theorem profile22_node33 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,1,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,1,9] 2 profile22_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,1,9] 2 profile22_node33_cert).mp (by decide +kernel))

def profile22_node34_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 6 9 28 41), lower := (rows 1 10 6 9 28 32), losses := [{ target := 0, region := (rows 0 26 30 8 26 32), good := (rows 0 30 22 30 30 32) }] }

theorem profile22_node34 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,1,12] 2 profile22_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,1,12] 2 profile22_node34_cert).mp (by decide +kernel))

def profile22_node32_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node32 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,1] 2 (by decide) (choices 2) [9,12] profile22_node32_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,1] (choices 2) [9,12] profile22_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node33
  · exact profile22_node34

def profile22_node36_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 6 12 25 41), lower := (rows 1 10 6 12 25 32), losses := [] }

theorem profile22_node36 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,4,9] 2 profile22_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,4,9] 2 profile22_node36_cert).mp (by decide +kernel))

def profile22_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node35 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,4] 2 (by decide) (choices 2) [9] profile22_node35_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2,4] (choices 2) [9] profile22_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node36

def profile22_node31_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node31 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2] 2 (by decide) (choices 1) [1,4] profile22_node31_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,2] (choices 1) [1,4] profile22_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node32
  · exact profile22_node35

def profile22_node39_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 12 9 19 44), lower := (rows 1 10 12 9 19 32), losses := [{ target := 0, region := (rows 0 14 14 8 16 46), good := (rows 0 46 46 46 54 32) }] }

theorem profile22_node39 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,3] 2 profile22_node39_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,3] 2 profile22_node39_cert).mp (by decide +kernel))

def profile22_node40_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 12 9 21 42), lower := (rows 1 10 12 9 21 32), losses := [{ target := 0, region := (rows 0 14 14 8 16 46), good := (rows 0 46 46 46 54 32) }] }

theorem profile22_node40 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,5] 2 profile22_node40_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,5] 2 profile22_node40_cert).mp (by decide +kernel))

def profile22_node42_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 10 12 9 22 41), lower := (rows 1 10 12 9 22 41), losses := [] }

theorem profile22_node42 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,6,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,6,9] 2 profile22_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,6,9] 2 profile22_node42_cert).mp (by decide +kernel))

def profile22_node41_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node41 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,6] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,6] 2 (by decide) (choices 2) [9] profile22_node41_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,6] (choices 2) [9] profile22_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node42

def profile22_node43_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 12 9 25 38), lower := (rows 1 10 12 9 25 32), losses := [] }

theorem profile22_node43 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,9] 2 profile22_node43_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,9] 2 profile22_node43_cert).mp (by decide +kernel))

def profile22_node44_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 12 9 26 37), lower := (rows 1 10 12 9 26 32), losses := [{ target := 0, region := (rows 0 30 30 8 30 32), good := (rows 0 30 30 30 30 32) }] }

theorem profile22_node44 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,10] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,10] 2 profile22_node44_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,10] 2 profile22_node44_cert).mp (by decide +kernel))

def profile22_node45_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 12 9 28 35), lower := (rows 1 10 12 9 28 32), losses := [{ target := 0, region := (rows 0 30 30 8 30 32), good := (rows 0 30 30 30 30 32) }] }

theorem profile22_node45 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,12] 2 profile22_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1,12] 2 profile22_node45_cert).mp (by decide +kernel))

def profile22_node38_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node38 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile22_node38_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,1] (choices 2) [3,5,6,9,10,12] profile22_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile22_node39
  · exact profile22_node40
  · exact profile22_node41
  · exact profile22_node43
  · exact profile22_node44
  · exact profile22_node45

def profile22_node47_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 12 10 21 41), lower := (rows 1 10 12 10 21 32), losses := [{ target := 3, region := (rows 63 2 4 0 20 32), good := (rows 1 3 21 3 21 33) }] }

theorem profile22_node47 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,2,5] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,2,5] 2 profile22_node47_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,2,5] 2 profile22_node47_cert).mp (by decide +kernel))

def profile22_node48_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 12 10 25 37), lower := (rows 1 10 12 10 25 32), losses := [] }

theorem profile22_node48 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,2,9] 2 profile22_node48_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,2,9] 2 profile22_node48_cert).mp (by decide +kernel))

def profile22_node46_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node46 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,2] 2 (by decide) (choices 2) [5,9] profile22_node46_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,2] (choices 2) [5,9] profile22_node46_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node47
  · exact profile22_node48

def profile22_node50_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 12 12 19 41), lower := (rows 1 10 12 12 19 32), losses := [{ target := 3, region := (rows 63 2 4 0 18 32), good := (rows 1 19 5 5 19 33) }] }

theorem profile22_node50 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,4,3] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,4,3] 2 profile22_node50_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,4,3] 2 profile22_node50_cert).mp (by decide +kernel))

def profile22_node51_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 12 12 25 35), lower := (rows 1 10 12 12 25 32), losses := [] }

theorem profile22_node51 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,4,9] 2 profile22_node51_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,4,9] 2 profile22_node51_cert).mp (by decide +kernel))

def profile22_node49_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node49 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,4] 2 (by decide) (choices 2) [3,9] profile22_node49_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8,4] (choices 2) [3,9] profile22_node49_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node50
  · exact profile22_node51

def profile22_node37_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node37 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8] 2 (by decide) (choices 1) [1,2,4] profile22_node37_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8,8] (choices 1) [1,2,4] profile22_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile22_node38
  · exact profile22_node46
  · exact profile22_node49

def profile22_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node20 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8] 2 (by decide) (choices 1) [1,2,8] profile22_node20_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0,8] (choices 1) [1,2,8] profile22_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile22_node21
  · exact profile22_node31
  · exact profile22_node37

def profile22_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node1 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0] 2 (by decide) (choices 1) [1,4,8] profile22_node1_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [0] (choices 1) [1,4,8] profile22_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile22_node2
  · exact profile22_node13
  · exact profile22_node20

def profile22_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile22_node0 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [] 2 := by
  apply routed_branch (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [] 2 (by decide) (choices 0) [0] profile22_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [] (choices 0) [0] profile22_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node1

theorem profile22 : Upper (D (n:=6) [2,9,9,11,16,16]) (R (n:=6) [2,9,9,11,16,16]) [] 2 := profile22_node0

def profile23_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 5 10 28 44), lower := (rows 1 3 5 10 28 44), losses := [] }

theorem profile23_node6 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,2,12,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,2,12,12] 2 profile23_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,2,12,12] 2 profile23_node6_cert).mp (by decide +kernel))

def profile23_node5_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node5 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,2,12] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,2,12] 2 (by decide) (choices 2) [12] profile23_node5_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,2,12] (choices 2) [12] profile23_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node6

def profile23_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node4 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,2] 2 (by decide) (choices 2) [12] profile23_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,2] (choices 2) [12] profile23_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node5

def profile23_node9_cert : Bound 6 := { allowed := (rows 0 0 0 0 5 0), upper := (rows 1 3 5 12 26 44), lower := (rows 1 3 5 12 26 44), losses := [{ target := 0, region := (rows 0 2 4 44 16 44), good := (rows 0 2 44 44 58 44) }] }

theorem profile23_node9 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4,10,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4,10,12] 2 profile23_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4,10,12] 2 profile23_node9_cert).mp (by decide +kernel))

def profile23_node8_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node8 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4,10] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4,10] 2 (by decide) (choices 2) [12] profile23_node8_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4,10] (choices 2) [12] profile23_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node9

def profile23_node10_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 5 12 28 42), lower := (rows 1 3 5 12 28 32), losses := [{ target := 0, region := (rows 0 2 4 28 28 32), good := (rows 0 2 28 28 28 32) },{ target := 2, region := (rows 63 63 0 8 16 56), good := (rows 3 3 3 43 59 35) }] }

theorem profile23_node10 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4,12] 2 profile23_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4,12] 2 profile23_node10_cert).mp (by decide +kernel))

def profile23_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node7 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4] 2 (by decide) (choices 2) [10,12] profile23_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1,4] (choices 2) [10,12] profile23_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node8
  · exact profile23_node10

def profile23_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node3 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1] 2 (by decide) (choices 1) [2,4] profile23_node3_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,1] (choices 1) [2,4] profile23_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node4
  · exact profile23_node7

def profile23_node14_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 6 9 28 44), lower := (rows 1 3 6 9 28 44), losses := [] }

theorem profile23_node14 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,1,12,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,1,12,12] 2 profile23_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,1,12,12] 2 profile23_node14_cert).mp (by decide +kernel))

def profile23_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node13 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,1,12] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,1,12] 2 (by decide) (choices 2) [12] profile23_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,1,12] (choices 2) [12] profile23_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node14

def profile23_node12_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node12 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,1] 2 (by decide) (choices 2) [12] profile23_node12_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,1] (choices 2) [12] profile23_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node13

def profile23_node16_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 12), upper := (rows 1 3 6 12 25 44), lower := (rows 1 3 6 12 25 32), losses := [{ target := 0, region := (rows 0 2 6 14 16 46), good := (rows 0 46 46 44 56 32) },{ target := 2, region := (rows 63 63 0 8 24 32), good := (rows 3 3 3 27 27 35) }] }

theorem profile23_node16 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,4,9] 2 profile23_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,4,9] 2 profile23_node16_cert).mp (by decide +kernel))

def profile23_node17_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 6 12 28 41), lower := (rows 1 3 6 12 28 32), losses := [{ target := 0, region := (rows 0 2 6 30 30 32), good := (rows 0 30 30 28 28 32) },{ target := 2, region := (rows 63 63 0 8 16 56), good := (rows 3 3 3 43 59 35) }] }

theorem profile23_node17 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,4,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,4,12] 2 profile23_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,4,12] 2 profile23_node17_cert).mp (by decide +kernel))

def profile23_node15_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node15 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,4] 2 (by decide) (choices 2) [9,12] profile23_node15_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2,4] (choices 2) [9,12] profile23_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node16
  · exact profile23_node17

def profile23_node11_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node11 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2] 2 (by decide) (choices 1) [1,4] profile23_node11_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,2] (choices 1) [1,4] profile23_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node12
  · exact profile23_node15

def profile23_node21_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 3 12 9 22 44), lower := (rows 1 3 12 9 22 44), losses := [{ target := 0, region := (rows 0 2 44 8 16 44), good := (rows 0 2 44 44 54 44) }] }

theorem profile23_node21 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1,6,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1,6,12] 2 profile23_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1,6,12] 2 profile23_node21_cert).mp (by decide +kernel))

def profile23_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node20 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1,6] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1,6] 2 (by decide) (choices 2) [12] profile23_node20_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1,6] (choices 2) [12] profile23_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node21

def profile23_node22_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 3 12 9 28 38), lower := (rows 1 3 12 9 28 32), losses := [{ target := 0, region := (rows 0 2 28 8 28 32), good := (rows 0 2 28 28 28 32) },{ target := 3, region := (rows 63 63 4 0 16 52), good := (rows 3 3 39 3 55 35) }] }

theorem profile23_node22 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1,12] 2 profile23_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1,12] 2 profile23_node22_cert).mp (by decide +kernel))

def profile23_node19_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node19 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1] 2 (by decide) (choices 2) [6,12] profile23_node19_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,1] (choices 2) [6,12] profile23_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node20
  · exact profile23_node22

def profile23_node24_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 12), upper := (rows 1 3 12 10 21 44), lower := (rows 1 3 12 10 21 32), losses := [{ target := 0, region := (rows 0 2 14 10 16 46), good := (rows 0 46 44 46 52 32) },{ target := 3, region := (rows 63 63 4 0 20 32), good := (rows 3 3 23 3 23 35) }] }

theorem profile23_node24 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,2,5] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,2,5] 2 profile23_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,2,5] 2 profile23_node24_cert).mp (by decide +kernel))

def profile23_node25_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 3 12 10 28 37), lower := (rows 1 3 12 10 28 32), losses := [{ target := 0, region := (rows 0 2 30 10 30 32), good := (rows 0 30 28 30 28 32) },{ target := 3, region := (rows 63 63 4 0 16 52), good := (rows 3 3 39 3 55 35) }] }

theorem profile23_node25 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,2,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,2,12] 2 profile23_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,2,12] 2 profile23_node25_cert).mp (by decide +kernel))

def profile23_node23_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node23 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,2] 2 (by decide) (choices 2) [5,12] profile23_node23_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,2] (choices 2) [5,12] profile23_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node24
  · exact profile23_node25

def profile23_node27_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 12), upper := (rows 1 3 12 12 19 44), lower := (rows 1 3 12 12 19 32), losses := [{ target := 0, region := (rows 0 2 63 63 16 63), good := (rows 44 46 44 44 62 44) },{ target := 2, region := (rows 63 63 0 8 63 32), good := (rows 19 19 27 27 19 51) },{ target := 3, region := (rows 63 63 4 0 63 32), good := (rows 19 19 23 23 19 51) }] }

theorem profile23_node27 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,3] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,3] 2 profile23_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,3] 2 profile23_node27_cert).mp (by decide +kernel))

def profile23_node28_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 3 12 12 21 42), lower := (rows 1 3 12 12 21 32), losses := [{ target := 0, region := (rows 0 2 63 63 16 34), good := (rows 12 46 12 12 28 44) },{ target := 2, region := (rows 63 63 0 8 16 44), good := (rows 3 3 43 43 51 35) }] }

theorem profile23_node28 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,5] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,5] 2 profile23_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,5] 2 profile23_node28_cert).mp (by decide +kernel))

def profile23_node29_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 12 22 41), lower := (rows 1 3 12 12 22 32), losses := [{ target := 0, region := (rows 0 2 63 63 18 32), good := (rows 12 30 12 12 30 44) },{ target := 2, region := (rows 63 63 0 8 16 44), good := (rows 3 3 43 43 51 35) },{ target := 3, region := (rows 63 63 4 0 28 32), good := (rows 3 3 23 23 23 35) }] }

theorem profile23_node29 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,6] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,6] 2 profile23_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,6] 2 profile23_node29_cert).mp (by decide +kernel))

def profile23_node30_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 12), upper := (rows 1 3 12 12 25 38), lower := (rows 1 3 12 12 25 32), losses := [{ target := 0, region := (rows 0 2 63 63 16 34), good := (rows 12 46 12 12 28 44) },{ target := 2, region := (rows 63 63 0 8 28 32), good := (rows 3 3 27 27 27 35) }] }

theorem profile23_node30 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,9] 2 profile23_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,9] 2 profile23_node30_cert).mp (by decide +kernel))

def profile23_node31_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 3 12 12 26 37), lower := (rows 1 3 12 12 26 32), losses := [{ target := 0, region := (rows 0 2 63 63 18 32), good := (rows 12 30 12 12 30 44) },{ target := 2, region := (rows 63 63 0 8 28 32), good := (rows 3 3 27 27 27 35) },{ target := 3, region := (rows 63 63 4 0 16 44), good := (rows 3 3 39 39 51 35) }] }

theorem profile23_node31 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,10] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,10] 2 profile23_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,10] 2 profile23_node31_cert).mp (by decide +kernel))

def profile23_node32_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 12 28 35), lower := (rows 1 3 12 12 28 32), losses := [{ target := 0, region := (rows 0 2 63 63 63 32), good := (rows 28 30 28 28 28 60) },{ target := 2, region := (rows 63 63 0 8 16 63), good := (rows 35 35 43 43 59 35) }] }

theorem profile23_node32 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,12] 2 profile23_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4,12] 2 profile23_node32_cert).mp (by decide +kernel))

def profile23_node26_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node26 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile23_node26_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8,4] (choices 2) [3,5,6,9,10,12] profile23_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node27
  · exact profile23_node28
  · exact profile23_node29
  · exact profile23_node30
  · exact profile23_node31
  · exact profile23_node32

def profile23_node18_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node18 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8] 2 (by decide) (choices 1) [1,2,4] profile23_node18_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1,8] (choices 1) [1,2,4] profile23_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node19
  · exact profile23_node23
  · exact profile23_node26

def profile23_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node2 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1] 2 (by decide) (choices 1) [1,2,8] profile23_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,1] (choices 1) [1,2,8] profile23_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node3
  · exact profile23_node11
  · exact profile23_node18

def profile23_node37_cert : Bound 6 := { allowed := (rows 0 0 0 0 4 1), upper := (rows 1 6 5 9 26 44), lower := (rows 1 6 5 9 26 44), losses := [{ target := 0, region := (rows 0 38 4 8 48 32), good := (rows 0 6 6 8 26 62) }] }

theorem profile23_node37 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1,10,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1,10,12] 2 profile23_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1,10,12] 2 profile23_node37_cert).mp (by decide +kernel))

def profile23_node36_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node36 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1,10] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1,10] 2 (by decide) (choices 2) [12] profile23_node36_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1,10] (choices 2) [12] profile23_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node37

def profile23_node38_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 8), upper := (rows 1 6 5 9 28 42), lower := (rows 1 6 5 9 28 32), losses := [{ target := 0, region := (rows 0 22 4 8 16 48), good := (rows 0 6 6 8 62 32) },{ target := 2, region := (rows 63 2 0 63 16 34), good := (rows 9 43 9 9 25 41) }] }

theorem profile23_node38 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1,12] 2 profile23_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1,12] 2 profile23_node38_cert).mp (by decide +kernel))

def profile23_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node35 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1] 2 (by decide) (choices 2) [10,12] profile23_node35_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,1] (choices 2) [10,12] profile23_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node36
  · exact profile23_node38

def profile23_node40_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 12), upper := (rows 1 6 5 10 25 44), lower := (rows 1 6 5 10 25 32), losses := [{ target := 0, region := (rows 0 6 4 14 16 38), good := (rows 0 46 46 42 24 32) },{ target := 2, region := (rows 63 2 0 10 26 32), good := (rows 1 27 1 27 25 33) }] }

theorem profile23_node40 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,2,9] 2 profile23_node40_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,2,9] 2 profile23_node40_cert).mp (by decide +kernel))

def profile23_node41_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 5 10 28 41), lower := (rows 1 6 5 10 28 32), losses := [{ target := 0, region := (rows 0 22 4 30 22 32), good := (rows 0 30 30 26 30 32) },{ target := 2, region := (rows 63 2 0 10 16 58), good := (rows 1 43 1 43 57 33) }] }

theorem profile23_node41 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,2,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,2,12] 2 profile23_node41_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,2,12] 2 profile23_node41_cert).mp (by decide +kernel))

def profile23_node39_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node39 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,2] 2 (by decide) (choices 2) [9,12] profile23_node39_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,2] (choices 2) [9,12] profile23_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node40
  · exact profile23_node41

def profile23_node43_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 12), upper := (rows 1 6 5 12 25 42), lower := (rows 1 6 5 12 25 32), losses := [{ target := 0, region := (rows 0 14 4 14 16 62), good := (rows 0 46 46 46 58 32) },{ target := 2, region := (rows 63 2 0 8 24 32), good := (rows 1 3 1 25 25 33) }] }

theorem profile23_node43 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4,9] 2 profile23_node43_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4,9] 2 profile23_node43_cert).mp (by decide +kernel))

def profile23_node45_cert : Bound 6 := { allowed := (rows 0 0 0 0 4 4), upper := (rows 1 6 5 12 26 41), lower := (rows 1 6 5 12 26 41), losses := [{ target := 0, region := (rows 0 14 4 14 62 32), good := (rows 0 30 30 30 26 58) }] }

theorem profile23_node45 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4,10,9] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4,10,9] 2 profile23_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4,10,9] 2 profile23_node45_cert).mp (by decide +kernel))

def profile23_node44_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node44 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4,10] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4,10] 2 (by decide) (choices 2) [9] profile23_node44_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4,10] (choices 2) [9] profile23_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node45

def profile23_node42_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node42 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4] 2 (by decide) (choices 2) [9,10] profile23_node42_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1,4] (choices 2) [9,10] profile23_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node43
  · exact profile23_node44

def profile23_node34_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node34 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1] 2 (by decide) (choices 1) [1,2,4] profile23_node34_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,1] (choices 1) [1,2,4] profile23_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node35
  · exact profile23_node39
  · exact profile23_node42

def profile23_node48_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 12), upper := (rows 1 6 6 9 25 44), lower := (rows 1 6 6 9 25 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 56), good := (rows 6 6 6 46 62 38) },{ target := 2, region := (rows 63 2 0 63 63 32), good := (rows 25 27 27 25 25 57) }] }

theorem profile23_node48 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,1,9] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,1,9] 2 profile23_node48_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,1,9] 2 profile23_node48_cert).mp (by decide +kernel))

def profile23_node49_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 6 9 28 41), lower := (rows 1 6 6 9 28 32), losses := [{ target := 0, region := (rows 0 63 63 8 24 32), good := (rows 6 6 6 30 30 38) },{ target := 2, region := (rows 63 2 0 63 16 63), good := (rows 41 43 43 41 57 41) }] }

theorem profile23_node49 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,1,12] 2 profile23_node49_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,1,12] 2 profile23_node49_cert).mp (by decide +kernel))

def profile23_node47_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node47 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,1] 2 (by decide) (choices 2) [9,12] profile23_node47_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,1] (choices 2) [9,12] profile23_node47_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node48
  · exact profile23_node49

def profile23_node51_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 6 12 25 41), lower := (rows 1 6 6 12 25 32), losses := [{ target := 2, region := (rows 63 2 0 8 24 56), good := (rows 1 3 3 57 57 33) }] }

theorem profile23_node51 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,4,9] 2 profile23_node51_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,4,9] 2 profile23_node51_cert).mp (by decide +kernel))

def profile23_node50_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node50 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,4] 2 (by decide) (choices 2) [9] profile23_node50_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2,4] (choices 2) [9] profile23_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node51

def profile23_node46_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node46 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2] 2 (by decide) (choices 1) [1,4] profile23_node46_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,2] (choices 1) [1,4] profile23_node46_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node47
  · exact profile23_node50

def profile23_node54_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 12), upper := (rows 1 6 12 9 19 44), lower := (rows 1 6 12 9 19 32), losses := [{ target := 0, region := (rows 0 14 12 8 16 44), good := (rows 0 38 46 46 18 32) },{ target := 2, region := (rows 63 2 0 63 18 32), good := (rows 9 27 9 9 27 41) },{ target := 3, region := (rows 63 6 4 0 22 32), good := (rows 1 23 23 1 19 33) }] }

theorem profile23_node54 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,3] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,3] 2 profile23_node54_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,3] 2 profile23_node54_cert).mp (by decide +kernel))

def profile23_node55_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 6 12 9 21 42), lower := (rows 1 6 12 9 21 32), losses := [{ target := 0, region := (rows 0 30 12 8 16 44), good := (rows 0 38 46 46 54 32) },{ target := 2, region := (rows 63 2 0 63 16 34), good := (rows 9 43 9 9 25 41) }] }

theorem profile23_node55 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,5] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,5] 2 profile23_node55_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,5] 2 profile23_node55_cert).mp (by decide +kernel))

def profile23_node56_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 9 22 41), lower := (rows 1 6 12 9 22 32), losses := [{ target := 0, region := (rows 0 30 12 8 30 32), good := (rows 0 22 30 30 22 32) },{ target := 2, region := (rows 63 2 0 63 16 63), good := (rows 41 43 41 41 59 41) },{ target := 3, region := (rows 63 22 4 0 22 32), good := (rows 1 23 23 1 23 33) }] }

theorem profile23_node56 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,6] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,6] 2 profile23_node56_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,6] 2 profile23_node56_cert).mp (by decide +kernel))

def profile23_node57_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 12), upper := (rows 1 6 12 9 25 38), lower := (rows 1 6 12 9 25 32), losses := [{ target := 0, region := (rows 0 30 28 8 16 62), good := (rows 0 38 46 46 62 32) },{ target := 2, region := (rows 63 2 0 63 63 32), good := (rows 25 27 25 25 25 57) }] }

theorem profile23_node57 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,9] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,9] 2 profile23_node57_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,9] 2 profile23_node57_cert).mp (by decide +kernel))

def profile23_node58_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 6 12 9 26 37), lower := (rows 1 6 12 9 26 32), losses := [{ target := 0, region := (rows 0 30 28 8 28 32), good := (rows 0 22 30 30 30 32) },{ target := 2, region := (rows 63 2 0 63 18 32), good := (rows 9 27 9 9 27 41) },{ target := 3, region := (rows 63 6 4 0 16 38), good := (rows 1 39 39 1 51 33) }] }

theorem profile23_node58 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,10] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,10] 2 profile23_node58_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,10] 2 profile23_node58_cert).mp (by decide +kernel))

def profile23_node59_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 9 28 35), lower := (rows 1 6 12 9 28 32), losses := [{ target := 0, region := (rows 0 30 28 8 28 32), good := (rows 0 22 30 30 30 32) },{ target := 2, region := (rows 63 2 0 63 16 34), good := (rows 9 43 9 9 25 41) }] }

theorem profile23_node59 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,12] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,12] 2 profile23_node59_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1,12] 2 profile23_node59_cert).mp (by decide +kernel))

def profile23_node53_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node53 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile23_node53_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,1] (choices 2) [3,5,6,9,10,12] profile23_node53_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node54
  · exact profile23_node55
  · exact profile23_node56
  · exact profile23_node57
  · exact profile23_node58
  · exact profile23_node59

def profile23_node61_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 10 21 41), lower := (rows 1 6 12 10 21 32), losses := [{ target := 2, region := (rows 63 2 0 10 16 46), good := (rows 1 43 41 43 49 33) },{ target := 3, region := (rows 63 22 4 0 22 32), good := (rows 1 23 23 19 23 33) }] }

theorem profile23_node61 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,2,5] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,2,5] 2 profile23_node61_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,2,5] 2 profile23_node61_cert).mp (by decide +kernel))

def profile23_node62_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 5), upper := (rows 1 6 12 10 25 37), lower := (rows 1 6 12 10 25 32), losses := [{ target := 2, region := (rows 63 2 0 10 30 32), good := (rows 1 27 25 27 25 33) },{ target := 3, region := (rows 63 6 4 0 16 38), good := (rows 1 39 39 35 17 33) }] }

theorem profile23_node62 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,2,9] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,2,9] 2 profile23_node62_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,2,9] 2 profile23_node62_cert).mp (by decide +kernel))

def profile23_node60_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node60 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,2] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,2] 2 (by decide) (choices 2) [5,9] profile23_node60_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,2] (choices 2) [5,9] profile23_node60_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node61
  · exact profile23_node62

def profile23_node64_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 12 19 41), lower := (rows 1 6 12 12 19 32), losses := [{ target := 2, region := (rows 63 2 0 8 18 44), good := (rows 1 51 41 41 19 33) },{ target := 3, region := (rows 63 14 4 0 30 32), good := (rows 1 23 23 23 19 33) }] }

theorem profile23_node64 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,4,3] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,4,3] 2 profile23_node64_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,4,3] 2 profile23_node64_cert).mp (by decide +kernel))

def profile23_node65_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 12 25 35), lower := (rows 1 6 12 12 25 32), losses := [{ target := 2, region := (rows 63 2 0 8 28 34), good := (rows 1 51 25 25 25 33) }] }

theorem profile23_node65 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,4,9] 2 :=
  bound_sound (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,4,9] 2 profile23_node65_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,4,9] 2 profile23_node65_cert).mp (by decide +kernel))

def profile23_node63_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node63 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,4] 2 (by decide) (choices 2) [3,9] profile23_node63_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8,4] (choices 2) [3,9] profile23_node63_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node64
  · exact profile23_node65

def profile23_node52_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node52 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8] 2 (by decide) (choices 1) [1,2,4] profile23_node52_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4,8] (choices 1) [1,2,4] profile23_node52_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node53
  · exact profile23_node60
  · exact profile23_node63

def profile23_node33_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node33 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4] 2 (by decide) (choices 1) [1,2,8] profile23_node33_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0,4] (choices 1) [1,2,8] profile23_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node34
  · exact profile23_node46
  · exact profile23_node52

def profile23_node1_route : Route 6 := (fun mask => match mask with | 8 => (4,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile23_node1 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0] 2 (by decide) (choices 1) [1,4] profile23_node1_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [0] (choices 1) [1,4] profile23_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile23_node2
  · exact profile23_node33

def profile23_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile23_node0 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [] 2 := by
  apply routed_branch (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [] 2 (by decide) (choices 0) [0] profile23_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [] (choices 0) [0] profile23_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node1

theorem profile23 : Upper (D (n:=6) [2,9,10,10,16,16]) (R (n:=6) [2,9,10,10,16,16]) [] 2 := profile23_node0

def profile24_node5_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 11 19 38), lower := (rows 1 2 5 11 19 32), losses := [] }

theorem profile24_node5 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,3,3] 2 :=
  bound_sound (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,3,3] 2 profile24_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,3,3] 2 profile24_node5_cert).mp (by decide +kernel))

def profile24_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 11 22 35), lower := (rows 1 2 5 11 22 32), losses := [{ target := 0, region := (rows 0 63 4 8 20 32), good := (rows 2 2 22 10 22 34) }] }

theorem profile24_node6 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,3,6] 2 :=
  bound_sound (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,3,6] 2 profile24_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,3,6] 2 profile24_node6_cert).mp (by decide +kernel))

def profile24_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile24_node4 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,3] 2 := by
  apply routed_branch (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,3] 2 (by decide) (choices 2) [3,6] profile24_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,3] (choices 2) [3,6] profile24_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile24_node5
  · exact profile24_node6

def profile24_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 5 14 19 35), lower := (rows 1 2 5 14 19 32), losses := [{ target := 0, region := (rows 0 63 4 12 16 32), good := (rows 2 2 14 14 18 34) }] }

theorem profile24_node8 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,6,3] 2 :=
  bound_sound (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,6,3] 2 profile24_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,6,3] 2 profile24_node8_cert).mp (by decide +kernel))

def profile24_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile24_node7 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,6] 2 := by
  apply routed_branch (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,6] 2 (by decide) (choices 2) [3] profile24_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1,6] (choices 2) [3] profile24_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node8

def profile24_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile24_node3 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1] 2 := by
  apply routed_branch (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1] 2 (by decide) (choices 2) [3,6] profile24_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,1] (choices 2) [3,6] profile24_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile24_node4
  · exact profile24_node7

def profile24_node11_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 11 19 37), lower := (rows 1 2 6 11 19 32), losses := [] }

theorem profile24_node11 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,3,3] 2 :=
  bound_sound (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,3,3] 2 profile24_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,3,3] 2 profile24_node11_cert).mp (by decide +kernel))

def profile24_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 11 21 35), lower := (rows 1 2 6 11 21 32), losses := [{ target := 1, region := (rows 63 0 4 8 20 32), good := (rows 1 1 21 9 21 33) }] }

theorem profile24_node12 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,3,5] 2 :=
  bound_sound (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,3,5] 2 profile24_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,3,5] 2 profile24_node12_cert).mp (by decide +kernel))

def profile24_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile24_node10 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,3] 2 := by
  apply routed_branch (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,3] 2 (by decide) (choices 2) [3,5] profile24_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,3] (choices 2) [3,5] profile24_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile24_node11
  · exact profile24_node12

def profile24_node14_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 3), upper := (rows 1 2 6 13 19 35), lower := (rows 1 2 6 13 19 32), losses := [{ target := 1, region := (rows 63 0 4 12 16 32), good := (rows 1 1 13 13 17 33) }] }

theorem profile24_node14 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,5,3] 2 :=
  bound_sound (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,5,3] 2 profile24_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,5,3] 2 profile24_node14_cert).mp (by decide +kernel))

def profile24_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile24_node13 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,5] 2 := by
  apply routed_branch (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,5] 2 (by decide) (choices 2) [3] profile24_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2,5] (choices 2) [3] profile24_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node14

def profile24_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile24_node9 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2] 2 := by
  apply routed_branch (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2] 2 (by decide) (choices 2) [3,5] profile24_node9_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0,2] (choices 2) [3,5] profile24_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile24_node10
  · exact profile24_node13

def profile24_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile24_node2 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0] 2 := by
  apply routed_branch (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0] 2 (by decide) (choices 1) [1,2] profile24_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0,0] (choices 1) [1,2] profile24_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile24_node3
  · exact profile24_node9

def profile24_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile24_node1 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0] 2 := by
  apply routed_branch (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0] 2 (by decide) (choices 0) [0] profile24_node1_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [0] (choices 0) [0] profile24_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node2

def profile24_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile24_node0 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [] 2 := by
  apply routed_branch (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [] 2 (by decide) (choices 0) [0] profile24_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [] (choices 0) [0] profile24_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node1

theorem profile24 : Upper (D (n:=6) [3,3,9,16,16,16]) (R (n:=6) [3,3,9,16,16,16]) [] 2 := profile24_node0

def profile25_node0_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 31 31 31 31 31 63), lower := (rows 1 2 4 8 16 32), losses := [] }

theorem profile25_node0 : Upper (D (n:=6) [3,9,9,9,9,24]) (R (n:=6) [3,9,9,9,9,24]) [] 2 :=
  bound_sound (D (n:=6) [3,9,9,9,9,24]) (R (n:=6) [3,9,9,9,9,24]) [] 2 profile25_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,9,9,24]) (R (n:=6) [3,9,9,9,9,24]) [] 2 profile25_node0_cert).mp (by decide +kernel))

theorem profile25 : Upper (D (n:=6) [3,9,9,9,9,24]) (R (n:=6) [3,9,9,9,9,24]) [] 2 := profile25_node0

def profile26_node0_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 47 47 47 47 63 47), lower := (rows 1 2 4 8 16 32), losses := [] }

theorem profile26_node0 : Upper (D (n:=6) [3,9,9,9,16,17]) (R (n:=6) [3,9,9,9,16,17]) [] 2 :=
  bound_sound (D (n:=6) [3,9,9,9,16,17]) (R (n:=6) [3,9,9,9,16,17]) [] 2 profile26_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,9,16,17]) (R (n:=6) [3,9,9,9,16,17]) [] 2 profile26_node0_cert).mp (by decide +kernel))

theorem profile26 : Upper (D (n:=6) [3,9,9,9,16,17]) (R (n:=6) [3,9,9,9,16,17]) [] 2 := profile26_node0

def profile27_node6_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 5 9 26 44), lower := (rows 1 3 5 9 26 44), losses := [] }

theorem profile27_node6 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,10,12] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,10,12] 2 profile27_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,10,12] 2 profile27_node6_cert).mp (by decide +kernel))

def profile27_node5_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node5 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,10] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,10] 2 (by decide) (choices 2) [12] profile27_node5_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,10] (choices 2) [12] profile27_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node6

def profile27_node8_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 5 9 28 42), lower := (rows 1 3 5 9 28 42), losses := [] }

theorem profile27_node8 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,12,10] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,12,10] 2 profile27_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,12,10] 2 profile27_node8_cert).mp (by decide +kernel))

def profile27_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node7 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,12] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,12] 2 (by decide) (choices 2) [10] profile27_node7_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1,12] (choices 2) [10] profile27_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node8

def profile27_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node4 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1] 2 (by decide) (choices 2) [10,12] profile27_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,1] (choices 2) [10,12] profile27_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node5
  · exact profile27_node7

def profile27_node10_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 5 10 25 44), lower := (rows 1 3 5 10 25 32), losses := [] }

theorem profile27_node10 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2,9] 2 profile27_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2,9] 2 profile27_node10_cert).mp (by decide +kernel))

def profile27_node12_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 3 5 10 28 41), lower := (rows 1 3 5 10 28 41), losses := [] }

theorem profile27_node12 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2,12,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2,12,9] 2 profile27_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2,12,9] 2 profile27_node12_cert).mp (by decide +kernel))

def profile27_node11_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node11 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2,12] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2,12] 2 (by decide) (choices 2) [9] profile27_node11_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2,12] (choices 2) [9] profile27_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node12

def profile27_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node9 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2] 2 (by decide) (choices 2) [9,12] profile27_node9_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,2] (choices 2) [9,12] profile27_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node10
  · exact profile27_node11

def profile27_node14_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 5 12 25 42), lower := (rows 1 3 5 12 25 32), losses := [] }

theorem profile27_node14 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4,9] 2 profile27_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4,9] 2 profile27_node14_cert).mp (by decide +kernel))

def profile27_node16_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 3 5 12 26 41), lower := (rows 1 3 5 12 26 41), losses := [] }

theorem profile27_node16 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4,10,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4,10,9] 2 profile27_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4,10,9] 2 profile27_node16_cert).mp (by decide +kernel))

def profile27_node15_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node15 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4,10] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4,10] 2 (by decide) (choices 2) [9] profile27_node15_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4,10] (choices 2) [9] profile27_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node16

def profile27_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node13 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4] 2 (by decide) (choices 2) [9,10] profile27_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1,4] (choices 2) [9,10] profile27_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node14
  · exact profile27_node15

def profile27_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node3 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1] 2 (by decide) (choices 1) [1,2,4] profile27_node3_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,1] (choices 1) [1,2,4] profile27_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile27_node4
  · exact profile27_node9
  · exact profile27_node13

def profile27_node19_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 6 9 25 44), lower := (rows 1 3 6 9 25 32), losses := [] }

theorem profile27_node19 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1,9] 2 profile27_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1,9] 2 profile27_node19_cert).mp (by decide +kernel))

def profile27_node21_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 3 6 9 28 41), lower := (rows 1 3 6 9 28 41), losses := [] }

theorem profile27_node21 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1,12,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1,12,9] 2 profile27_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1,12,9] 2 profile27_node21_cert).mp (by decide +kernel))

def profile27_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node20 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1,12] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1,12] 2 (by decide) (choices 2) [9] profile27_node20_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1,12] (choices 2) [9] profile27_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node21

def profile27_node18_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node18 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1] 2 (by decide) (choices 2) [9,12] profile27_node18_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,1] (choices 2) [9,12] profile27_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node19
  · exact profile27_node20

def profile27_node23_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 6 12 25 41), lower := (rows 1 3 6 12 25 32), losses := [] }

theorem profile27_node23 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,4,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,4,9] 2 profile27_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,4,9] 2 profile27_node23_cert).mp (by decide +kernel))

def profile27_node22_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node22 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,4] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,4] 2 (by decide) (choices 2) [9] profile27_node22_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2,4] (choices 2) [9] profile27_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node23

def profile27_node17_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node17 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2] 2 (by decide) (choices 1) [1,4] profile27_node17_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,2] (choices 1) [1,4] profile27_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node18
  · exact profile27_node22

def profile27_node26_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 3 12 9 19 44), lower := (rows 1 3 12 9 19 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 44), good := (rows 0 2 44 44 18 32) }] }

theorem profile27_node26 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,3] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,3] 2 profile27_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,3] 2 profile27_node26_cert).mp (by decide +kernel))

def profile27_node27_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 9 21 42), lower := (rows 1 3 12 9 21 32), losses := [{ target := 3, region := (rows 63 63 4 0 20 32), good := (rows 3 3 23 3 23 35) }] }

theorem profile27_node27 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,5] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,5] 2 profile27_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,5] 2 profile27_node27_cert).mp (by decide +kernel))

def profile27_node29_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 3 12 9 22 41), lower := (rows 1 3 12 9 22 41), losses := [] }

theorem profile27_node29 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,6,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,6,9] 2 profile27_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,6,9] 2 profile27_node29_cert).mp (by decide +kernel))

def profile27_node28_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node28 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,6] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,6] 2 (by decide) (choices 2) [9] profile27_node28_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,6] (choices 2) [9] profile27_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node29

def profile27_node30_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 9 25 38), lower := (rows 1 3 12 9 25 32), losses := [] }

theorem profile27_node30 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,9] 2 profile27_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,9] 2 profile27_node30_cert).mp (by decide +kernel))

def profile27_node31_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 3 12 9 26 37), lower := (rows 1 3 12 9 26 32), losses := [{ target := 3, region := (rows 63 63 4 0 16 36), good := (rows 3 3 39 3 19 35) }] }

theorem profile27_node31 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,10] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,10] 2 profile27_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,10] 2 profile27_node31_cert).mp (by decide +kernel))

def profile27_node32_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 9 28 35), lower := (rows 1 3 12 9 28 32), losses := [{ target := 0, region := (rows 0 2 28 8 28 32), good := (rows 0 2 28 28 28 32) }] }

theorem profile27_node32 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,12] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,12] 2 profile27_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1,12] 2 profile27_node32_cert).mp (by decide +kernel))

def profile27_node25_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node25 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile27_node25_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,1] (choices 2) [3,5,6,9,10,12] profile27_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile27_node26
  · exact profile27_node27
  · exact profile27_node28
  · exact profile27_node30
  · exact profile27_node31
  · exact profile27_node32

def profile27_node34_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 10 21 41), lower := (rows 1 3 12 10 21 32), losses := [{ target := 3, region := (rows 63 63 4 0 20 32), good := (rows 3 3 23 3 23 35) }] }

theorem profile27_node34 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,2,5] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,2,5] 2 profile27_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,2,5] 2 profile27_node34_cert).mp (by decide +kernel))

def profile27_node35_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 10 25 37), lower := (rows 1 3 12 10 25 32), losses := [] }

theorem profile27_node35 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,2,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,2,9] 2 profile27_node35_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,2,9] 2 profile27_node35_cert).mp (by decide +kernel))

def profile27_node33_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node33 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,2] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,2] 2 (by decide) (choices 2) [5,9] profile27_node33_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,2] (choices 2) [5,9] profile27_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node34
  · exact profile27_node35

def profile27_node37_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 12 19 41), lower := (rows 1 3 12 12 19 32), losses := [{ target := 3, region := (rows 63 63 4 0 63 32), good := (rows 19 19 23 23 19 51) }] }

theorem profile27_node37 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,4,3] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,4,3] 2 profile27_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,4,3] 2 profile27_node37_cert).mp (by decide +kernel))

def profile27_node38_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 3 12 12 25 35), lower := (rows 1 3 12 12 25 32), losses := [] }

theorem profile27_node38 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,4,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,4,9] 2 profile27_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,4,9] 2 profile27_node38_cert).mp (by decide +kernel))

def profile27_node36_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node36 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,4] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,4] 2 (by decide) (choices 2) [3,9] profile27_node36_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8,4] (choices 2) [3,9] profile27_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node37
  · exact profile27_node38

def profile27_node24_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node24 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8] 2 (by decide) (choices 1) [1,2,4] profile27_node24_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1,8] (choices 1) [1,2,4] profile27_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile27_node25
  · exact profile27_node33
  · exact profile27_node36

def profile27_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node2 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1] 2 (by decide) (choices 1) [1,2,8] profile27_node2_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,1] (choices 1) [1,2,8] profile27_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile27_node3
  · exact profile27_node17
  · exact profile27_node24

def profile27_node42_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 5 9 25 42), lower := (rows 1 6 5 9 25 32), losses := [] }

theorem profile27_node42 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1,9] 2 profile27_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1,9] 2 profile27_node42_cert).mp (by decide +kernel))

def profile27_node44_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 0), upper := (rows 1 6 5 9 26 41), lower := (rows 1 6 5 9 26 41), losses := [] }

theorem profile27_node44 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1,10,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1,10,9] 2 profile27_node44_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1,10,9] 2 profile27_node44_cert).mp (by decide +kernel))

def profile27_node43_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node43 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1,10] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1,10] 2 (by decide) (choices 2) [9] profile27_node43_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1,10] (choices 2) [9] profile27_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node44

def profile27_node41_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node41 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1] 2 (by decide) (choices 2) [9,10] profile27_node41_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,1] (choices 2) [9,10] profile27_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node42
  · exact profile27_node43

def profile27_node46_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 5 10 25 41), lower := (rows 1 6 5 10 25 32), losses := [] }

theorem profile27_node46 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,2,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,2,9] 2 profile27_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,2,9] 2 profile27_node46_cert).mp (by decide +kernel))

def profile27_node45_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node45 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,2] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,2] 2 (by decide) (choices 2) [9] profile27_node45_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1,2] (choices 2) [9] profile27_node45_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node46

def profile27_node40_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node40 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1] 2 (by decide) (choices 1) [1,2] profile27_node40_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,1] (choices 1) [1,2] profile27_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node41
  · exact profile27_node45

def profile27_node49_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 6 9 25 41), lower := (rows 1 6 6 9 25 32), losses := [] }

theorem profile27_node49 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,2,1,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,2,1,9] 2 profile27_node49_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,2,1,9] 2 profile27_node49_cert).mp (by decide +kernel))

def profile27_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node48 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,2,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,2,1] 2 (by decide) (choices 2) [9] profile27_node48_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,2,1] (choices 2) [9] profile27_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node49

def profile27_node47_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node47 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,2] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,2] 2 (by decide) (choices 1) [1] profile27_node47_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,2] (choices 1) [1] profile27_node47_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node48

def profile27_node52_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 9 19 41), lower := (rows 1 6 12 9 19 32), losses := [{ target := 3, region := (rows 63 6 4 0 22 32), good := (rows 1 23 23 1 19 33) }] }

theorem profile27_node52 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8,1,3] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8,1,3] 2 profile27_node52_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8,1,3] 2 profile27_node52_cert).mp (by decide +kernel))

def profile27_node53_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 6 12 9 25 35), lower := (rows 1 6 12 9 25 32), losses := [] }

theorem profile27_node53 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8,1,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8,1,9] 2 profile27_node53_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8,1,9] 2 profile27_node53_cert).mp (by decide +kernel))

def profile27_node51_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node51 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8,1] 2 (by decide) (choices 2) [3,9] profile27_node51_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8,1] (choices 2) [3,9] profile27_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node52
  · exact profile27_node53

def profile27_node50_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node50 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8] 2 (by decide) (choices 1) [1] profile27_node50_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4,8] (choices 1) [1] profile27_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node51

def profile27_node39_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node39 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4] 2 (by decide) (choices 1) [1,2,8] profile27_node39_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,4] (choices 1) [1,2,8] profile27_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile27_node40
  · exact profile27_node47
  · exact profile27_node50

def profile27_node57_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 9 19 44), lower := (rows 1 10 5 9 19 32), losses := [{ target := 3, region := (rows 63 2 63 0 18 32), good := (rows 5 23 5 5 23 37) }] }

theorem profile27_node57 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,3] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,3] 2 profile27_node57_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,3] 2 profile27_node57_cert).mp (by decide +kernel))

def profile27_node58_cert : Bound 6 := { allowed := (rows 0 0 0 0 8 8), upper := (rows 1 10 5 9 21 42), lower := (rows 1 10 5 9 21 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 42), good := (rows 0 42 4 42 20 32) }] }

theorem profile27_node58 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,5] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,5] 2 profile27_node58_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,5] 2 profile27_node58_cert).mp (by decide +kernel))

def profile27_node60_cert : Bound 6 := { allowed := (rows 0 0 0 0 9 0), upper := (rows 1 10 5 9 22 41), lower := (rows 1 10 5 9 22 41), losses := [] }

theorem profile27_node60 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,6,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,6,9] 2 profile27_node60_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,6,9] 2 profile27_node60_cert).mp (by decide +kernel))

def profile27_node59_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node59 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,6] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,6] 2 (by decide) (choices 2) [9] profile27_node59_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,6] (choices 2) [9] profile27_node59_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node60

def profile27_node61_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 9 25 38), lower := (rows 1 10 5 9 25 32), losses := [] }

theorem profile27_node61 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,9] 2 profile27_node61_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,9] 2 profile27_node61_cert).mp (by decide +kernel))

def profile27_node62_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 9 26 37), lower := (rows 1 10 5 9 26 32), losses := [{ target := 0, region := (rows 0 26 4 8 26 32), good := (rows 0 26 4 26 26 32) }] }

theorem profile27_node62 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,10] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,10] 2 profile27_node62_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,10] 2 profile27_node62_cert).mp (by decide +kernel))

def profile27_node63_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 1 10 5 9 28 35), lower := (rows 1 10 5 9 28 32), losses := [{ target := 3, region := (rows 63 2 63 0 16 34), good := (rows 5 39 5 5 21 37) }] }

theorem profile27_node63 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,12] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,12] 2 profile27_node63_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1,12] 2 profile27_node63_cert).mp (by decide +kernel))

def profile27_node56_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node56 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile27_node56_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,1] (choices 2) [3,5,6,9,10,12] profile27_node56_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile27_node57
  · exact profile27_node58
  · exact profile27_node59
  · exact profile27_node61
  · exact profile27_node62
  · exact profile27_node63

def profile27_node65_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 10 21 41), lower := (rows 1 10 5 10 21 32), losses := [{ target := 3, region := (rows 63 2 63 0 63 32), good := (rows 21 23 21 23 21 53) }] }

theorem profile27_node65 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,2,5] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,2,5] 2 profile27_node65_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,2,5] 2 profile27_node65_cert).mp (by decide +kernel))

def profile27_node66_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 10 25 37), lower := (rows 1 10 5 10 25 32), losses := [] }

theorem profile27_node66 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,2,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,2,9] 2 profile27_node66_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,2,9] 2 profile27_node66_cert).mp (by decide +kernel))

def profile27_node64_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node64 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,2] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,2] 2 (by decide) (choices 2) [5,9] profile27_node64_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,2] (choices 2) [5,9] profile27_node64_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node65
  · exact profile27_node66

def profile27_node68_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 12 19 41), lower := (rows 1 10 5 12 19 32), losses := [{ target := 3, region := (rows 63 2 63 0 18 32), good := (rows 5 23 5 5 23 37) }] }

theorem profile27_node68 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,4,3] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,4,3] 2 profile27_node68_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,4,3] 2 profile27_node68_cert).mp (by decide +kernel))

def profile27_node69_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 5 12 25 35), lower := (rows 1 10 5 12 25 32), losses := [] }

theorem profile27_node69 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,4,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,4,9] 2 profile27_node69_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,4,9] 2 profile27_node69_cert).mp (by decide +kernel))

def profile27_node67_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node67 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,4] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,4] 2 (by decide) (choices 2) [3,9] profile27_node67_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1,4] (choices 2) [3,9] profile27_node67_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node68
  · exact profile27_node69

def profile27_node55_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node55 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1] 2 (by decide) (choices 1) [1,2,4] profile27_node55_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,1] (choices 1) [1,2,4] profile27_node55_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile27_node56
  · exact profile27_node64
  · exact profile27_node67

def profile27_node72_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 6 9 21 41), lower := (rows 1 10 6 9 21 32), losses := [{ target := 3, region := (rows 63 2 6 0 22 32), good := (rows 1 23 23 1 21 33) }] }

theorem profile27_node72 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2,1,5] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2,1,5] 2 profile27_node72_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2,1,5] 2 profile27_node72_cert).mp (by decide +kernel))

def profile27_node73_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 9), upper := (rows 1 10 6 9 25 37), lower := (rows 1 10 6 9 25 32), losses := [] }

theorem profile27_node73 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2,1,9] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2,1,9] 2 profile27_node73_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2,1,9] 2 profile27_node73_cert).mp (by decide +kernel))

def profile27_node71_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node71 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2,1] 2 (by decide) (choices 2) [5,9] profile27_node71_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2,1] (choices 2) [5,9] profile27_node71_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node72
  · exact profile27_node73

def profile27_node70_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node70 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2] 2 (by decide) (choices 1) [1] profile27_node70_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,2] (choices 1) [1] profile27_node70_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node71

def profile27_node76_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 10 12 9 19 37), lower := (rows 1 10 12 9 19 32), losses := [{ target := 3, region := (rows 63 2 4 0 18 36), good := (rows 1 19 37 1 19 33) }] }

theorem profile27_node76 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8,1,3] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8,1,3] 2 profile27_node76_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8,1,3] 2 profile27_node76_cert).mp (by decide +kernel))

def profile27_node77_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 1), upper := (rows 1 10 12 9 21 35), lower := (rows 1 10 12 9 21 32), losses := [{ target := 3, region := (rows 63 2 4 0 20 34), good := (rows 1 35 21 1 21 33) }] }

theorem profile27_node77 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8,1,5] 2 :=
  bound_sound (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8,1,5] 2 profile27_node77_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8,1,5] 2 profile27_node77_cert).mp (by decide +kernel))

def profile27_node75_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node75 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8,1] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8,1] 2 (by decide) (choices 2) [3,5] profile27_node75_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8,1] (choices 2) [3,5] profile27_node75_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node76
  · exact profile27_node77

def profile27_node74_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node74 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8] 2 (by decide) (choices 1) [1] profile27_node74_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8,8] (choices 1) [1] profile27_node74_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node75

def profile27_node54_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node54 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8] 2 (by decide) (choices 1) [1,2,8] profile27_node54_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0,8] (choices 1) [1,2,8] profile27_node54_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile27_node55
  · exact profile27_node70
  · exact profile27_node74

def profile27_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node1 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0] 2 (by decide) (choices 1) [1,4,8] profile27_node1_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [0] (choices 1) [1,4,8] profile27_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile27_node2
  · exact profile27_node39
  · exact profile27_node54

def profile27_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile27_node0 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [] 2 := by
  apply routed_branch (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [] 2 (by decide) (choices 0) [0] profile27_node0_route
    (by change RowCover 6 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [] (choices 0) [0] profile27_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node1

theorem profile27 : Upper (D (n:=6) [3,9,9,10,16,16]) (R (n:=6) [3,9,9,10,16,16]) [] 2 := profile27_node0

def profile28_node0_cert : Bound 6 := { allowed := (rows 0 0 0 0 1 1), upper := (rows 15 15 15 15 31 47), lower := (rows 1 2 4 8 16 32), losses := [] }

theorem profile28_node0 : Upper (D (n:=6) [4,9,9,9,16,16]) (R (n:=6) [4,9,9,9,16,16]) [] 2 :=
  bound_sound (D (n:=6) [4,9,9,9,16,16]) (R (n:=6) [4,9,9,9,16,16]) [] 2 profile28_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [4,9,9,9,16,16]) (R (n:=6) [4,9,9,9,16,16]) [] 2 profile28_node0_cert).mp (by decide +kernel))

theorem profile28 : Upper (D (n:=6) [4,9,9,9,16,16]) (R (n:=6) [4,9,9,9,16,16]) [] 2 := profile28_node0

def profile29_node0_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 0), upper := (rows 63 63 63 63 63 63), lower := (rows 1 2 4 8 16 32), losses := [] }

theorem profile29_node0 : Upper (D (n:=6) [9,9,9,9,9,18]) (R (n:=6) [9,9,9,9,9,18]) [] 2 :=
  bound_sound (D (n:=6) [9,9,9,9,9,18]) (R (n:=6) [9,9,9,9,9,18]) [] 2 profile29_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [9,9,9,9,9,18]) (R (n:=6) [9,9,9,9,9,18]) [] 2 profile29_node0_cert).mp (by decide +kernel))

theorem profile29 : Upper (D (n:=6) [9,9,9,9,9,18]) (R (n:=6) [9,9,9,9,9,18]) [] 2 := profile29_node0

def profile30_node0_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 16), upper := (rows 63 63 63 63 63 63), lower := (rows 1 2 4 8 16 32), losses := [] }

theorem profile30_node0 : Upper (D (n:=6) [9,9,9,9,10,17]) (R (n:=6) [9,9,9,9,10,17]) [] 2 :=
  bound_sound (D (n:=6) [9,9,9,9,10,17]) (R (n:=6) [9,9,9,9,10,17]) [] 2 profile30_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [9,9,9,9,10,17]) (R (n:=6) [9,9,9,9,10,17]) [] 2 profile30_node0_cert).mp (by decide +kernel))

theorem profile30 : Upper (D (n:=6) [9,9,9,9,10,17]) (R (n:=6) [9,9,9,9,10,17]) [] 2 := profile30_node0

def profile31_node0_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 16), upper := (rows 31 31 31 31 31 63), lower := (rows 1 2 4 8 16 32), losses := [] }

theorem profile31_node0 : Upper (D (n:=6) [9,9,9,9,11,16]) (R (n:=6) [9,9,9,9,11,16]) [] 2 :=
  bound_sound (D (n:=6) [9,9,9,9,11,16]) (R (n:=6) [9,9,9,9,11,16]) [] 2 profile31_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [9,9,9,9,11,16]) (R (n:=6) [9,9,9,9,11,16]) [] 2 profile31_node0_cert).mp (by decide +kernel))

theorem profile31 : Upper (D (n:=6) [9,9,9,9,11,16]) (R (n:=6) [9,9,9,9,11,16]) [] 2 := profile31_node0

def profile32_node0_cert : Bound 6 := { allowed := (rows 0 0 0 0 0 24), upper := (rows 31 31 31 31 31 63), lower := (rows 1 2 4 8 16 32), losses := [] }

theorem profile32_node0 : Upper (D (n:=6) [9,9,9,10,10,16]) (R (n:=6) [9,9,9,10,10,16]) [] 2 :=
  bound_sound (D (n:=6) [9,9,9,10,10,16]) (R (n:=6) [9,9,9,10,10,16]) [] 2 profile32_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [9,9,9,10,10,16]) (R (n:=6) [9,9,9,10,10,16]) [] 2 profile32_node0_cert).mp (by decide +kernel))

theorem profile32 : Upper (D (n:=6) [9,9,9,10,10,16]) (R (n:=6) [9,9,9,10,10,16]) [] 2 := profile32_node0

def catalogue : List (List Nat) := [[2,2,2,9,16,32],[2,2,2,9,24,24],[2,2,2,16,16,25],[2,2,2,16,17,24],[2,2,3,16,16,24],[2,2,9,9,9,32],[2,2,9,9,16,25],[2,2,9,9,17,24],[2,2,9,10,16,24],[2,2,9,16,16,18],[2,2,9,16,17,17],[2,2,10,16,16,17],[2,2,11,16,16,16],[2,3,9,9,16,24],[2,3,9,16,16,17],[2,3,10,16,16,16],[2,4,9,16,16,16],[2,9,9,9,9,25],[2,9,9,9,10,24],[2,9,9,9,16,18],[2,9,9,9,17,17],[2,9,9,10,16,17],[2,9,9,11,16,16],[2,9,10,10,16,16],[3,3,9,16,16,16],[3,9,9,9,9,24],[3,9,9,9,16,17],[3,9,9,10,16,16],[4,9,9,9,16,16],[9,9,9,9,9,18],[9,9,9,9,10,17],[9,9,9,9,11,16],[9,9,9,10,10,16]]

theorem catalogue_eq : profiles 6 6 0 7 7=catalogue := by decide +kernel

theorem profile_upper (xs : List Nat) (member : xs∈profiles 6 6 0 7 7) :
    Upper (n:=6) (D xs) (R xs) [] 2 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
theorem upper (E : Graph (Fin 6)) (loops : Loopless E) (budget : arcCount E=7)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x) : score E≤2 := by
  have od (x) : SparseSupport.outdegree E x<6 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<6 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 6).map (SparseSupport.outdegree E)).sum=7 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 6).map (SparseSupport.indegree E)).sum=7 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    (by decide) od idg degree td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetSevenOrder6
