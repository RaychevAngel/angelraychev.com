import SmallRowPrefixBoolean
import SmallDegreeProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
7 vertices with seven arrows and total degree at least two at each vertex. -/
namespace Delivery.SmallBudgetSevenOrder7
open FiniteGame Extremal RowPrefix SmallDegreeProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e f g : Nat) : Rows 7 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => g

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16,32,64]
  | 2 => [3,5,9,17,33,65,6,10,18,34,66,12,20,36,68,24,40,72,48,80,96]
  | 3 => [7,11,19,35,67,13,21,37,69,25,41,73,49,81,97,14,22,38,70,26,42,74,50,82,98,28,44,76,52,84,100,56,88,104,112]
  | 4 => [15,23,39,71,27,43,75,51,83,99,29,45,77,53,85,101,57,89,105,113,30,46,78,54,86,102,58,90,106,114,60,92,108,116,120]
  | 5 => [31,47,79,55,87,103,59,91,107,115,61,93,109,117,121,62,94,110,118,122,124]
  | 6 => [63,95,111,119,123,125,126]
  | 7 => [127]
  | _ => []

theorem cover (d : Fin 8) : RowCover 7 d.val (choices d.val) := by
  revert d
  decide +kernel

def profile0_node6_cert : Bound 7 := { allowed := (rows 0 0 0 0 4 0 4), upper := (rows 1 2 4 9 19 38 76), lower := (rows 1 2 4 9 19 38 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 72), good := (rows 38 38 38 110 54 38 102) },{ target := 1, region := (rows 127 0 127 127 16 32 127), good := (rows 77 77 77 77 93 109 77) }] }

theorem profile0_node6 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,3,6] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,3,6] 2 profile0_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,3,6] 2 profile0_node6_cert).mp (by decide +kernel))

def profile0_node7_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 9 19 44 70), lower := (rows 1 2 4 9 19 44 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 40 127), good := (rows 70 70 70 110 86 110 70) },{ target := 1, region := (rows 127 0 127 127 16 127 64), good := (rows 45 45 45 45 61 45 109) },{ target := 2, region := (rows 127 127 0 127 127 32 64), good := (rows 27 27 27 27 27 59 91) }] }

theorem profile0_node7 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,3,12] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,3,12] 2 profile0_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,3,12] 2 profile0_node7_cert).mp (by decide +kernel))

def profile0_node5_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node5 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,3] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,3] 2 (by decide) (choices 2) [6,12] profile0_node5_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,3] (choices 2) [6,12] profile0_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node6
  · exact profile0_node7

def profile0_node9_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 9 21 38 74), lower := (rows 1 2 4 9 21 38 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 72), good := (rows 38 38 38 110 54 38 102) },{ target := 1, region := (rows 127 0 127 127 127 32 64), good := (rows 29 29 29 29 29 61 93) }] }

theorem profile0_node9 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,5,6] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,5,6] 2 profile0_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,5,6] 2 profile0_node9_cert).mp (by decide +kernel))

def profile0_node10_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 9 21 42 70), lower := (rows 1 2 4 9 21 42 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 40 127), good := (rows 70 70 70 110 86 110 70) },{ target := 1, region := (rows 127 0 127 127 127 32 64), good := (rows 29 29 29 29 29 61 93) },{ target := 2, region := (rows 127 127 0 127 16 127 64), good := (rows 43 43 43 43 59 43 107) }] }

theorem profile0_node10 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,5,10] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,5,10] 2 profile0_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,5,10] 2 profile0_node10_cert).mp (by decide +kernel))

def profile0_node8_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node8 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,5] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,5] 2 (by decide) (choices 2) [6,10] profile0_node8_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,5] (choices 2) [6,10] profile0_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node9
  · exact profile0_node10

def profile0_node12_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 4 4), upper := (rows 1 2 4 9 22 35 76), lower := (rows 1 2 4 9 22 35 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 32 72), good := (rows 22 22 22 94 22 54 86) },{ target := 1, region := (rows 127 0 127 127 16 32 127), good := (rows 77 77 77 77 93 109 77) }] }

theorem profile0_node12 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,3] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,3] 2 profile0_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,3] 2 profile0_node12_cert).mp (by decide +kernel))

def profile0_node13_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 9 22 37 74), lower := (rows 1 2 4 9 22 37 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 32 72), good := (rows 22 22 22 94 22 54 86) },{ target := 1, region := (rows 127 0 127 127 16 127 64), good := (rows 45 45 45 45 61 45 109) }] }

theorem profile0_node13 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,5] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,5] 2 profile0_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,5] 2 profile0_node13_cert).mp (by decide +kernel))

def profile0_node14_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 9 22 38 73), lower := (rows 1 2 4 9 22 38 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 127 64), good := (rows 54 54 54 62 54 54 118) },{ target := 1, region := (rows 127 0 127 127 16 32 127), good := (rows 77 77 77 77 93 109 77) }] }

theorem profile0_node14 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,6] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,6] 2 profile0_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,6] 2 profile0_node14_cert).mp (by decide +kernel))

def profile0_node15_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 9 22 41 70), lower := (rows 1 2 4 9 22 41 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 32 127), good := (rows 86 86 86 94 86 126 86) },{ target := 1, region := (rows 127 0 127 127 16 127 64), good := (rows 45 45 45 45 61 45 109) },{ target := 2, region := (rows 127 127 0 127 16 127 64), good := (rows 43 43 43 43 59 43 107) }] }

theorem profile0_node15 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,9] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,9] 2 profile0_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,9] 2 profile0_node15_cert).mp (by decide +kernel))

def profile0_node16_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 9 22 42 69), lower := (rows 1 2 4 9 22 42 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 40 64), good := (rows 22 22 22 62 22 62 86) },{ target := 1, region := (rows 127 0 127 127 16 32 127), good := (rows 77 77 77 77 93 109 77) },{ target := 2, region := (rows 127 127 0 127 16 127 64), good := (rows 43 43 43 43 59 43 107) }] }

theorem profile0_node16 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,10] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,10] 2 profile0_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,10] 2 profile0_node16_cert).mp (by decide +kernel))

def profile0_node17_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 4 9 22 44 67), lower := (rows 1 2 4 9 22 44 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 40 64), good := (rows 22 22 22 62 22 62 86) },{ target := 1, region := (rows 127 0 127 127 16 127 64), good := (rows 45 45 45 45 61 45 109) },{ target := 2, region := (rows 127 127 0 127 16 32 127), good := (rows 75 75 75 75 91 107 75) }] }

theorem profile0_node17 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,12] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,12] 2 profile0_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6,12] 2 profile0_node17_cert).mp (by decide +kernel))

def profile0_node11_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node11 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile0_node11_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,6] (choices 2) [3,5,6,9,10,12] profile0_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node12
  · exact profile0_node13
  · exact profile0_node14
  · exact profile0_node15
  · exact profile0_node16
  · exact profile0_node17

def profile0_node19_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 9 25 38 70), lower := (rows 1 2 4 9 25 38 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 126 102 102) },{ target := 1, region := (rows 127 0 127 127 127 32 64), good := (rows 29 29 29 29 29 61 93) },{ target := 2, region := (rows 127 127 0 127 127 32 64), good := (rows 27 27 27 27 27 59 91) }] }

theorem profile0_node19 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,9,6] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,9,6] 2 profile0_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,9,6] 2 profile0_node19_cert).mp (by decide +kernel))

def profile0_node18_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node18 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,9] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,9] 2 (by decide) (choices 2) [6] profile0_node18_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,9] (choices 2) [6] profile0_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node19

def profile0_node21_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 9 26 37 70), lower := (rows 1 2 4 9 26 37 64), losses := [{ target := 0, region := (rows 0 127 127 8 24 32 127), good := (rows 70 70 70 94 94 102 70) },{ target := 1, region := (rows 127 0 127 127 16 127 64), good := (rows 45 45 45 45 61 45 109) },{ target := 2, region := (rows 127 127 0 127 127 32 64), good := (rows 27 27 27 27 27 59 91) }] }

theorem profile0_node21 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,10,5] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,10,5] 2 profile0_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,10,5] 2 profile0_node21_cert).mp (by decide +kernel))

def profile0_node22_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 9 26 38 69), lower := (rows 1 2 4 9 26 38 64), losses := [{ target := 0, region := (rows 0 127 127 8 24 127 64), good := (rows 38 38 38 62 62 38 102) },{ target := 1, region := (rows 127 0 127 127 16 32 127), good := (rows 77 77 77 77 93 109 77) },{ target := 2, region := (rows 127 127 0 127 127 32 64), good := (rows 27 27 27 27 27 59 91) }] }

theorem profile0_node22 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,10,6] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,10,6] 2 profile0_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,10,6] 2 profile0_node22_cert).mp (by decide +kernel))

def profile0_node20_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node20 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,10] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,10] 2 (by decide) (choices 2) [5,6] profile0_node20_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,10] (choices 2) [5,6] profile0_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node21
  · exact profile0_node22

def profile0_node24_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 9 28 35 70), lower := (rows 1 2 4 9 28 35 64), losses := [{ target := 0, region := (rows 0 127 127 8 24 32 127), good := (rows 70 70 70 94 94 102 70) },{ target := 1, region := (rows 127 0 127 127 127 32 64), good := (rows 29 29 29 29 29 61 93) },{ target := 2, region := (rows 127 127 0 127 16 127 64), good := (rows 43 43 43 43 59 43 107) }] }

theorem profile0_node24 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,12,3] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,12,3] 2 profile0_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,12,3] 2 profile0_node24_cert).mp (by decide +kernel))

def profile0_node25_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 4 9 28 38 67), lower := (rows 1 2 4 9 28 38 64), losses := [{ target := 0, region := (rows 0 127 127 8 24 127 64), good := (rows 38 38 38 62 62 38 102) },{ target := 1, region := (rows 127 0 127 127 127 32 64), good := (rows 29 29 29 29 29 61 93) },{ target := 2, region := (rows 127 127 0 127 16 32 127), good := (rows 75 75 75 75 91 107 75) }] }

theorem profile0_node25 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,12,6] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,12,6] 2 profile0_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,12,6] 2 profile0_node25_cert).mp (by decide +kernel))

def profile0_node23_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node23 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,12] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,12] 2 (by decide) (choices 2) [3,6] profile0_node23_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1,12] (choices 2) [3,6] profile0_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node24
  · exact profile0_node25

def profile0_node4_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node4 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile0_node4_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,1] (choices 2) [3,5,6,9,10,12] profile0_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node5
  · exact profile0_node8
  · exact profile0_node11
  · exact profile0_node18
  · exact profile0_node20
  · exact profile0_node23

def profile0_node28_cert : Bound 7 := { allowed := (rows 0 0 0 0 4 0 4), upper := (rows 1 2 4 10 19 37 76), lower := (rows 1 2 4 10 19 37 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 110 78) },{ target := 1, region := (rows 127 0 127 8 16 127 72), good := (rows 37 37 37 109 53 37 101) }] }

theorem profile0_node28 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,3,5] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,3,5] 2 profile0_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,3,5] 2 profile0_node28_cert).mp (by decide +kernel))

def profile0_node29_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 10 19 44 69), lower := (rows 1 2 4 10 19 44 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) },{ target := 1, region := (rows 127 0 127 8 16 40 127), good := (rows 69 69 69 109 85 109 69) },{ target := 2, region := (rows 127 127 0 127 127 32 64), good := (rows 27 27 27 27 27 59 91) }] }

theorem profile0_node29 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,3,12] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,3,12] 2 profile0_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,3,12] 2 profile0_node29_cert).mp (by decide +kernel))

def profile0_node27_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node27 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,3] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,3] 2 (by decide) (choices 2) [5,12] profile0_node27_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,3] (choices 2) [5,12] profile0_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node28
  · exact profile0_node29

def profile0_node31_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 4 4), upper := (rows 1 2 4 10 21 35 76), lower := (rows 1 2 4 10 21 35 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 110 78) },{ target := 1, region := (rows 127 0 127 8 127 32 72), good := (rows 21 21 21 93 21 53 85) }] }

theorem profile0_node31 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,3] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,3] 2 profile0_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,3] 2 profile0_node31_cert).mp (by decide +kernel))

def profile0_node32_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 10 21 37 74), lower := (rows 1 2 4 10 21 37 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 110 78) },{ target := 1, region := (rows 127 0 127 8 127 127 64), good := (rows 53 53 53 61 53 53 117) }] }

theorem profile0_node32 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,5] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,5] 2 profile0_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,5] 2 profile0_node32_cert).mp (by decide +kernel))

def profile0_node33_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 10 21 38 73), lower := (rows 1 2 4 10 21 38 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) },{ target := 1, region := (rows 127 0 127 8 127 32 72), good := (rows 21 21 21 93 21 53 85) }] }

theorem profile0_node33 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,6] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,6] 2 profile0_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,6] 2 profile0_node33_cert).mp (by decide +kernel))

def profile0_node34_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 10 21 41 70), lower := (rows 1 2 4 10 21 41 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 110 78) },{ target := 1, region := (rows 127 0 127 8 127 40 64), good := (rows 21 21 21 61 21 61 85) },{ target := 2, region := (rows 127 127 0 127 16 127 64), good := (rows 43 43 43 43 59 43 107) }] }

theorem profile0_node34 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,9] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,9] 2 profile0_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,9] 2 profile0_node34_cert).mp (by decide +kernel))

def profile0_node35_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 10 21 42 69), lower := (rows 1 2 4 10 21 42 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) },{ target := 1, region := (rows 127 0 127 8 127 32 127), good := (rows 85 85 85 93 85 125 85) },{ target := 2, region := (rows 127 127 0 127 16 127 64), good := (rows 43 43 43 43 59 43 107) }] }

theorem profile0_node35 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,10] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,10] 2 profile0_node35_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,10] 2 profile0_node35_cert).mp (by decide +kernel))

def profile0_node36_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 4 10 21 44 67), lower := (rows 1 2 4 10 21 44 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) },{ target := 1, region := (rows 127 0 127 8 127 40 64), good := (rows 21 21 21 61 21 61 85) },{ target := 2, region := (rows 127 127 0 127 16 32 127), good := (rows 75 75 75 75 91 107 75) }] }

theorem profile0_node36 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,12] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,12] 2 profile0_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5,12] 2 profile0_node36_cert).mp (by decide +kernel))

def profile0_node30_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node30 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile0_node30_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,5] (choices 2) [3,5,6,9,10,12] profile0_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node31
  · exact profile0_node32
  · exact profile0_node33
  · exact profile0_node34
  · exact profile0_node35
  · exact profile0_node36

def profile0_node38_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 10 22 37 73), lower := (rows 1 2 4 10 22 37 64), losses := [{ target := 0, region := (rows 0 127 127 127 127 32 64), good := (rows 30 30 30 30 30 62 94) },{ target := 1, region := (rows 127 0 127 8 16 127 72), good := (rows 37 37 37 109 53 37 101) }] }

theorem profile0_node38 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,6,5] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,6,5] 2 profile0_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,6,5] 2 profile0_node38_cert).mp (by decide +kernel))

def profile0_node39_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 10 22 41 69), lower := (rows 1 2 4 10 22 41 64), losses := [{ target := 0, region := (rows 0 127 127 127 127 32 64), good := (rows 30 30 30 30 30 62 94) },{ target := 1, region := (rows 127 0 127 8 16 40 127), good := (rows 69 69 69 109 85 109 69) },{ target := 2, region := (rows 127 127 0 127 16 127 64), good := (rows 43 43 43 43 59 43 107) }] }

theorem profile0_node39 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,6,9] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,6,9] 2 profile0_node39_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,6,9] 2 profile0_node39_cert).mp (by decide +kernel))

def profile0_node37_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node37 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,6] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,6] 2 (by decide) (choices 2) [5,9] profile0_node37_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,6] (choices 2) [5,9] profile0_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node38
  · exact profile0_node39

def profile0_node41_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 10 25 37 70), lower := (rows 1 2 4 10 25 37 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 110 78) },{ target := 1, region := (rows 127 0 127 8 24 127 64), good := (rows 37 37 37 61 61 37 101) },{ target := 2, region := (rows 127 127 0 127 127 32 64), good := (rows 27 27 27 27 27 59 91) }] }

theorem profile0_node41 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,9,5] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,9,5] 2 profile0_node41_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,9,5] 2 profile0_node41_cert).mp (by decide +kernel))

def profile0_node42_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 10 25 38 69), lower := (rows 1 2 4 10 25 38 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) },{ target := 1, region := (rows 127 0 127 8 24 32 127), good := (rows 69 69 69 93 93 101 69) },{ target := 2, region := (rows 127 127 0 127 127 32 64), good := (rows 27 27 27 27 27 59 91) }] }

theorem profile0_node42 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,9,6] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,9,6] 2 profile0_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,9,6] 2 profile0_node42_cert).mp (by decide +kernel))

def profile0_node40_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node40 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,9] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,9] 2 (by decide) (choices 2) [5,6] profile0_node40_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,9] (choices 2) [5,6] profile0_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node41
  · exact profile0_node42

def profile0_node44_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 10 26 37 69), lower := (rows 1 2 4 10 26 37 64), losses := [{ target := 0, region := (rows 0 127 127 127 127 32 64), good := (rows 30 30 30 30 30 62 94) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 125 101 101) },{ target := 2, region := (rows 127 127 0 127 127 32 64), good := (rows 27 27 27 27 27 59 91) }] }

theorem profile0_node44 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,10,5] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,10,5] 2 profile0_node44_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,10,5] 2 profile0_node44_cert).mp (by decide +kernel))

def profile0_node43_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node43 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,10] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,10] 2 (by decide) (choices 2) [5] profile0_node43_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,10] (choices 2) [5] profile0_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node44

def profile0_node46_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 10 28 35 69), lower := (rows 1 2 4 10 28 35 64), losses := [{ target := 0, region := (rows 0 127 127 127 127 32 64), good := (rows 30 30 30 30 30 62 94) },{ target := 1, region := (rows 127 0 127 8 24 32 127), good := (rows 69 69 69 93 93 101 69) },{ target := 2, region := (rows 127 127 0 127 16 127 64), good := (rows 43 43 43 43 59 43 107) }] }

theorem profile0_node46 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,12,3] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,12,3] 2 profile0_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,12,3] 2 profile0_node46_cert).mp (by decide +kernel))

def profile0_node47_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 4 10 28 37 67), lower := (rows 1 2 4 10 28 37 64), losses := [{ target := 0, region := (rows 0 127 127 127 127 32 64), good := (rows 30 30 30 30 30 62 94) },{ target := 1, region := (rows 127 0 127 8 24 127 64), good := (rows 37 37 37 61 61 37 101) },{ target := 2, region := (rows 127 127 0 127 16 32 127), good := (rows 75 75 75 75 91 107 75) }] }

theorem profile0_node47 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,12,5] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,12,5] 2 profile0_node47_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,12,5] 2 profile0_node47_cert).mp (by decide +kernel))

def profile0_node45_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node45 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,12] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,12] 2 (by decide) (choices 2) [3,5] profile0_node45_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2,12] (choices 2) [3,5] profile0_node45_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node46
  · exact profile0_node47

def profile0_node26_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node26 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile0_node26_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,2] (choices 2) [3,5,6,9,10,12] profile0_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node27
  · exact profile0_node30
  · exact profile0_node37
  · exact profile0_node40
  · exact profile0_node43
  · exact profile0_node45

def profile0_node50_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 4), upper := (rows 1 2 4 12 19 35 76), lower := (rows 1 2 4 12 19 35 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 110 78) },{ target := 1, region := (rows 127 0 127 127 16 32 127), good := (rows 77 77 77 77 93 109 77) },{ target := 2, region := (rows 127 127 0 8 127 127 64), good := (rows 51 51 51 59 51 51 115) }] }

theorem profile0_node50 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,3] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,3] 2 profile0_node50_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,3] 2 profile0_node50_cert).mp (by decide +kernel))

def profile0_node51_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 4 12 19 37 74), lower := (rows 1 2 4 12 19 37 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 110 78) },{ target := 1, region := (rows 127 0 127 127 16 127 64), good := (rows 45 45 45 45 61 45 109) },{ target := 2, region := (rows 127 127 0 8 127 32 72), good := (rows 19 19 19 91 19 51 83) }] }

theorem profile0_node51 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,5] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,5] 2 profile0_node51_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,5] 2 profile0_node51_cert).mp (by decide +kernel))

def profile0_node52_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 4 12 19 38 73), lower := (rows 1 2 4 12 19 38 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) },{ target := 1, region := (rows 127 0 127 127 16 32 127), good := (rows 77 77 77 77 93 109 77) },{ target := 2, region := (rows 127 127 0 8 127 32 72), good := (rows 19 19 19 91 19 51 83) }] }

theorem profile0_node52 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,6] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,6] 2 profile0_node52_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,6] 2 profile0_node52_cert).mp (by decide +kernel))

def profile0_node53_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 12 19 41 70), lower := (rows 1 2 4 12 19 41 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 110 78) },{ target := 1, region := (rows 127 0 127 127 16 127 64), good := (rows 45 45 45 45 61 45 109) },{ target := 2, region := (rows 127 127 0 8 127 40 64), good := (rows 19 19 19 59 19 59 83) }] }

theorem profile0_node53 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,9] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,9] 2 profile0_node53_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,9] 2 profile0_node53_cert).mp (by decide +kernel))

def profile0_node54_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 12 19 42 69), lower := (rows 1 2 4 12 19 42 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) },{ target := 1, region := (rows 127 0 127 127 16 32 127), good := (rows 77 77 77 77 93 109 77) },{ target := 2, region := (rows 127 127 0 8 127 40 64), good := (rows 19 19 19 59 19 59 83) }] }

theorem profile0_node54 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,10] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,10] 2 profile0_node54_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,10] 2 profile0_node54_cert).mp (by decide +kernel))

def profile0_node55_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 4 12 19 44 67), lower := (rows 1 2 4 12 19 44 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) },{ target := 1, region := (rows 127 0 127 127 16 127 64), good := (rows 45 45 45 45 61 45 109) },{ target := 2, region := (rows 127 127 0 8 127 32 127), good := (rows 83 83 83 91 83 123 83) }] }

theorem profile0_node55 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,12] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,12] 2 profile0_node55_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3,12] 2 profile0_node55_cert).mp (by decide +kernel))

def profile0_node49_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node49 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile0_node49_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,3] (choices 2) [3,5,6,9,10,12] profile0_node49_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node50
  · exact profile0_node51
  · exact profile0_node52
  · exact profile0_node53
  · exact profile0_node54
  · exact profile0_node55

def profile0_node57_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 4 12 21 35 74), lower := (rows 1 2 4 12 21 35 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 110 78) },{ target := 1, region := (rows 127 0 127 127 127 32 64), good := (rows 29 29 29 29 29 61 93) },{ target := 2, region := (rows 127 127 0 8 16 127 72), good := (rows 35 35 35 107 51 35 99) }] }

theorem profile0_node57 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,5,3] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,5,3] 2 profile0_node57_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,5,3] 2 profile0_node57_cert).mp (by decide +kernel))

def profile0_node58_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 4 12 21 42 67), lower := (rows 1 2 4 12 21 42 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) },{ target := 1, region := (rows 127 0 127 127 127 32 64), good := (rows 29 29 29 29 29 61 93) },{ target := 2, region := (rows 127 127 0 8 16 40 127), good := (rows 67 67 67 107 83 107 67) }] }

theorem profile0_node58 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,5,10] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,5,10] 2 profile0_node58_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,5,10] 2 profile0_node58_cert).mp (by decide +kernel))

def profile0_node56_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node56 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,5] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,5] 2 (by decide) (choices 2) [3,10] profile0_node56_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,5] (choices 2) [3,10] profile0_node56_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node57
  · exact profile0_node58

def profile0_node60_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 4 12 22 35 73), lower := (rows 1 2 4 12 22 35 64), losses := [{ target := 0, region := (rows 0 127 127 127 127 32 64), good := (rows 30 30 30 30 30 62 94) },{ target := 1, region := (rows 127 0 127 127 16 32 127), good := (rows 77 77 77 77 93 109 77) },{ target := 2, region := (rows 127 127 0 8 16 127 72), good := (rows 35 35 35 107 51 35 99) }] }

theorem profile0_node60 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,6,3] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,6,3] 2 profile0_node60_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,6,3] 2 profile0_node60_cert).mp (by decide +kernel))

def profile0_node61_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 4 12 22 41 67), lower := (rows 1 2 4 12 22 41 64), losses := [{ target := 0, region := (rows 0 127 127 127 127 32 64), good := (rows 30 30 30 30 30 62 94) },{ target := 1, region := (rows 127 0 127 127 16 127 64), good := (rows 45 45 45 45 61 45 109) },{ target := 2, region := (rows 127 127 0 8 16 40 127), good := (rows 67 67 67 107 83 107 67) }] }

theorem profile0_node61 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,6,9] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,6,9] 2 profile0_node61_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,6,9] 2 profile0_node61_cert).mp (by decide +kernel))

def profile0_node59_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node59 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,6] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,6] 2 (by decide) (choices 2) [3,9] profile0_node59_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,6] (choices 2) [3,9] profile0_node59_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node60
  · exact profile0_node61

def profile0_node63_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 6), upper := (rows 1 2 4 12 25 35 70), lower := (rows 1 2 4 12 25 35 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 110 78) },{ target := 1, region := (rows 127 0 127 127 127 32 64), good := (rows 29 29 29 29 29 61 93) },{ target := 2, region := (rows 127 127 0 8 24 127 64), good := (rows 35 35 35 59 59 35 99) }] }

theorem profile0_node63 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,9,3] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,9,3] 2 profile0_node63_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,9,3] 2 profile0_node63_cert).mp (by decide +kernel))

def profile0_node64_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 4 12 25 38 67), lower := (rows 1 2 4 12 25 38 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) },{ target := 1, region := (rows 127 0 127 127 127 32 64), good := (rows 29 29 29 29 29 61 93) },{ target := 2, region := (rows 127 127 0 8 24 32 127), good := (rows 67 67 67 91 91 99 67) }] }

theorem profile0_node64 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,9,6] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,9,6] 2 profile0_node64_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,9,6] 2 profile0_node64_cert).mp (by decide +kernel))

def profile0_node62_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node62 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,9] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,9] 2 (by decide) (choices 2) [3,6] profile0_node62_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,9] (choices 2) [3,6] profile0_node62_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node63
  · exact profile0_node64

def profile0_node66_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 5), upper := (rows 1 2 4 12 26 35 69), lower := (rows 1 2 4 12 26 35 64), losses := [{ target := 0, region := (rows 0 127 127 127 127 32 64), good := (rows 30 30 30 30 30 62 94) },{ target := 1, region := (rows 127 0 127 127 16 32 127), good := (rows 77 77 77 77 93 109 77) },{ target := 2, region := (rows 127 127 0 8 24 127 64), good := (rows 35 35 35 59 59 35 99) }] }

theorem profile0_node66 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,10,3] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,10,3] 2 profile0_node66_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,10,3] 2 profile0_node66_cert).mp (by decide +kernel))

def profile0_node67_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 4 12 26 37 67), lower := (rows 1 2 4 12 26 37 64), losses := [{ target := 0, region := (rows 0 127 127 127 127 32 64), good := (rows 30 30 30 30 30 62 94) },{ target := 1, region := (rows 127 0 127 127 16 127 64), good := (rows 45 45 45 45 61 45 109) },{ target := 2, region := (rows 127 127 0 8 24 32 127), good := (rows 67 67 67 91 91 99 67) }] }

theorem profile0_node67 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,10,5] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,10,5] 2 profile0_node67_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,10,5] 2 profile0_node67_cert).mp (by decide +kernel))

def profile0_node65_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node65 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,10] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,10] 2 (by decide) (choices 2) [3,5] profile0_node65_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,10] (choices 2) [3,5] profile0_node65_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node66
  · exact profile0_node67

def profile0_node69_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 4 12 28 35 67), lower := (rows 1 2 4 12 28 35 64), losses := [{ target := 0, region := (rows 0 127 127 127 127 32 64), good := (rows 30 30 30 30 30 62 94) },{ target := 1, region := (rows 127 0 127 127 127 32 64), good := (rows 29 29 29 29 29 61 93) },{ target := 2, region := (rows 127 127 0 8 16 127 127), good := (rows 99 99 99 107 123 99 99) }] }

theorem profile0_node69 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,12,3] 2 :=
  bound_sound (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,12,3] 2 profile0_node69_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,12,3] 2 profile0_node69_cert).mp (by decide +kernel))

def profile0_node68_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node68 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,12] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,12] 2 (by decide) (choices 2) [3] profile0_node68_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4,12] (choices 2) [3] profile0_node68_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node69

def profile0_node48_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node48 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile0_node48_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0,4] (choices 2) [3,5,6,9,10,12] profile0_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node49
  · exact profile0_node56
  · exact profile0_node59
  · exact profile0_node62
  · exact profile0_node65
  · exact profile0_node68

def profile0_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node3 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0] 2 (by decide) (choices 1) [1,2,4] profile0_node3_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0,0] (choices 1) [1,2,4] profile0_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node4
  · exact profile0_node26
  · exact profile0_node48

def profile0_node2_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node2 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0] 2 (by decide) (choices 0) [0] profile0_node2_route
    (by change RowCover 7 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0,0] (choices 0) [0] profile0_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node3

def profile0_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node1 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0] 2 (by decide) (choices 0) [0] profile0_node1_route
    (by change RowCover 7 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [0] (choices 0) [0] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node2

def profile0_node0_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node0 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [] 2 := by
  apply routed_branch (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [] 2 (by decide) (choices 0) [0] profile0_node0_route
    (by change RowCover 7 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [] (choices 0) [0] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=7) [2,2,2,9,16,16,16]) (R (n:=7) [2,2,2,9,16,16,16]) [] 2 := profile0_node0

def profile1_node6_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 9 18 38 88), lower := (rows 1 2 5 9 18 38 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 36 72), good := (rows 18 18 54 90 18 54 82) }] }

theorem profile1_node6 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,6] 2 profile1_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,6] 2 profile1_node6_cert).mp (by decide +kernel))

def profile1_node7_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 9 18 42 84), lower := (rows 1 2 5 9 18 42 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 40 68), good := (rows 18 18 86 58 18 58 82) }] }

theorem profile1_node7 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,10] 2 profile1_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,10] 2 profile1_node7_cert).mp (by decide +kernel))

def profile1_node8_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 1 2), upper := (rows 1 2 5 9 18 44 82), lower := (rows 1 2 5 9 18 44 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 32 127), good := (rows 82 82 86 90 82 126 82) },{ target := 1, region := (rows 127 0 127 127 16 127 64), good := (rows 45 45 45 45 61 45 109) }] }

theorem profile1_node8 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,12] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,12] 2 profile1_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,12] 2 profile1_node8_cert).mp (by decide +kernel))

def profile1_node9_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 9 18 50 76), lower := (rows 1 2 5 9 18 50 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 64), good := (rows 50 50 54 58 50 50 114) }] }

theorem profile1_node9 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,18] 2 profile1_node9_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,18] 2 profile1_node9_cert).mp (by decide +kernel))

def profile1_node10_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 9 18 52 74), lower := (rows 1 2 5 9 18 52 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 36 72), good := (rows 18 18 54 90 18 54 82) }] }

theorem profile1_node10 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,20] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,20] 2 profile1_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,20] 2 profile1_node10_cert).mp (by decide +kernel))

def profile1_node11_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 9 18 56 70), lower := (rows 1 2 5 9 18 56 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 40 68), good := (rows 18 18 86 58 18 58 82) }] }

theorem profile1_node11 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,24] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,24] 2 profile1_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2,24] 2 profile1_node11_cert).mp (by decide +kernel))

def profile1_node5_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node5 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2] 2 (by decide) (choices 2) [6,10,12,18,20,24] profile1_node5_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,2] (choices 2) [6,10,12,18,20,24] profile1_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node6
  · exact profile1_node7
  · exact profile1_node8
  · exact profile1_node9
  · exact profile1_node10
  · exact profile1_node11

def profile1_node13_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 9 20 42 82), lower := (rows 1 2 5 9 20 42 64), losses := [{ target := 0, region := (rows 0 127 4 8 20 40 84), good := (rows 2 2 86 42 86 42 66) }] }

theorem profile1_node13 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,4,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,4,10] 2 profile1_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,4,10] 2 profile1_node13_cert).mp (by decide +kernel))

def profile1_node14_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 9 20 50 74), lower := (rows 1 2 5 9 20 50 64), losses := [{ target := 0, region := (rows 0 127 4 8 20 52 72), good := (rows 2 2 54 74 54 50 66) }] }

theorem profile1_node14 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,4,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,4,18] 2 profile1_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,4,18] 2 profile1_node14_cert).mp (by decide +kernel))

def profile1_node12_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node12 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,4] 2 (by decide) (choices 2) [10,18] profile1_node12_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,4] (choices 2) [10,18] profile1_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node13
  · exact profile1_node14

def profile1_node16_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 9 24 38 82), lower := (rows 1 2 5 9 24 38 64), losses := [{ target := 0, region := (rows 0 127 4 8 24 36 88), good := (rows 2 2 38 90 90 38 66) }] }

theorem profile1_node16 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,8,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,8,6] 2 profile1_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,8,6] 2 profile1_node16_cert).mp (by decide +kernel))

def profile1_node17_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 9 24 50 70), lower := (rows 1 2 5 9 24 50 64), losses := [{ target := 0, region := (rows 0 127 4 8 24 56 68), good := (rows 2 2 70 58 58 50 66) }] }

theorem profile1_node17 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,8,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,8,18] 2 profile1_node17_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,8,18] 2 profile1_node17_cert).mp (by decide +kernel))

def profile1_node15_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node15 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,8] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,8] 2 (by decide) (choices 2) [6,18] profile1_node15_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1,8] (choices 2) [6,18] profile1_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node16
  · exact profile1_node17

def profile1_node4_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node4 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1] 2 (by decide) (choices 1) [2,4,8] profile1_node4_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,1] (choices 1) [2,4,8] profile1_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node5
  · exact profile1_node12
  · exact profile1_node15

def profile1_node20_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 10 17 38 88), lower := (rows 1 2 5 10 17 38 64), losses := [{ target := 0, region := (rows 0 127 4 127 16 36 80), good := (rows 10 10 46 10 90 46 74) }] }

theorem profile1_node20 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,6] 2 profile1_node20_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,6] 2 profile1_node20_cert).mp (by decide +kernel))

def profile1_node21_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 10 17 42 84), lower := (rows 1 2 5 10 17 42 64), losses := [{ target := 0, region := (rows 0 127 4 127 16 127 64), good := (rows 42 42 46 42 58 42 106) }] }

theorem profile1_node21 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,10] 2 profile1_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,10] 2 profile1_node21_cert).mp (by decide +kernel))

def profile1_node22_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 10 17 44 82), lower := (rows 1 2 5 10 17 44 64), losses := [{ target := 0, region := (rows 0 127 4 127 16 36 80), good := (rows 10 10 46 10 90 46 74) }] }

theorem profile1_node22 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,12] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,12] 2 profile1_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,12] 2 profile1_node22_cert).mp (by decide +kernel))

def profile1_node23_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 10 17 50 76), lower := (rows 1 2 5 10 17 50 64), losses := [{ target := 0, region := (rows 0 127 4 127 16 48 68), good := (rows 10 10 78 10 58 58 74) }] }

theorem profile1_node23 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,18] 2 profile1_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,18] 2 profile1_node23_cert).mp (by decide +kernel))

def profile1_node24_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 1 2), upper := (rows 1 2 5 10 17 52 74), lower := (rows 1 2 5 10 17 52 64), losses := [{ target := 0, region := (rows 0 127 4 127 16 32 127), good := (rows 74 74 78 74 90 126 74) },{ target := 1, region := (rows 127 0 127 8 127 127 64), good := (rows 53 53 53 61 53 53 117) }] }

theorem profile1_node24 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,20] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,20] 2 profile1_node24_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,20] 2 profile1_node24_cert).mp (by decide +kernel))

def profile1_node25_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 10 17 56 70), lower := (rows 1 2 5 10 17 56 64), losses := [{ target := 0, region := (rows 0 127 4 127 16 48 68), good := (rows 10 10 78 10 58 58 74) }] }

theorem profile1_node25 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,24] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,24] 2 profile1_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1,24] 2 profile1_node25_cert).mp (by decide +kernel))

def profile1_node19_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node19 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1] 2 (by decide) (choices 2) [6,10,12,18,20,24] profile1_node19_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,1] (choices 2) [6,10,12,18,20,24] profile1_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node20
  · exact profile1_node21
  · exact profile1_node22
  · exact profile1_node23
  · exact profile1_node24
  · exact profile1_node25

def profile1_node27_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 10 18 37 88), lower := (rows 1 2 5 10 18 37 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 32 127), good := (rows 90 90 94 90 90 126 90) }] }

theorem profile1_node27 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,5] 2 profile1_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,5] 2 profile1_node27_cert).mp (by decide +kernel))

def profile1_node28_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 10 18 41 84), lower := (rows 1 2 5 10 18 41 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 32 68), good := (rows 26 26 94 26 26 58 90) }] }

theorem profile1_node28 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,9] 2 profile1_node28_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,9] 2 profile1_node28_cert).mp (by decide +kernel))

def profile1_node29_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 5 10 18 44 81), lower := (rows 1 2 5 10 18 44 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 36 64), good := (rows 26 26 62 26 26 62 90) },{ target := 1, region := (rows 127 0 127 8 16 40 80), good := (rows 5 5 5 45 85 45 69) }] }

theorem profile1_node29 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,12] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,12] 2 profile1_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,12] 2 profile1_node29_cert).mp (by decide +kernel))

def profile1_node30_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 10 18 49 76), lower := (rows 1 2 5 10 18 49 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 32 68), good := (rows 26 26 94 26 26 58 90) }] }

theorem profile1_node30 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,17] 2 profile1_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,17] 2 profile1_node30_cert).mp (by decide +kernel))

def profile1_node31_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 5 10 18 52 73), lower := (rows 1 2 5 10 18 52 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 36 64), good := (rows 26 26 62 26 26 62 90) },{ target := 1, region := (rows 127 0 127 8 16 48 72), good := (rows 5 5 5 77 53 53 69) }] }

theorem profile1_node31 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,20] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,20] 2 profile1_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,20] 2 profile1_node31_cert).mp (by decide +kernel))

def profile1_node32_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 1), upper := (rows 1 2 5 10 18 56 69), lower := (rows 1 2 5 10 18 56 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 127 64), good := (rows 58 58 62 58 58 58 122) },{ target := 1, region := (rows 127 0 127 8 16 32 127), good := (rows 69 69 69 77 85 125 69) }] }

theorem profile1_node32 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,24] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,24] 2 profile1_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2,24] 2 profile1_node32_cert).mp (by decide +kernel))

def profile1_node26_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node26 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2] 2 (by decide) (choices 2) [5,9,12,17,20,24] profile1_node26_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,2] (choices 2) [5,9,12,17,20,24] profile1_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node27
  · exact profile1_node28
  · exact profile1_node29
  · exact profile1_node30
  · exact profile1_node31
  · exact profile1_node32

def profile1_node34_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 10 20 35 88), lower := (rows 1 2 5 10 20 35 64), losses := [] }

theorem profile1_node34 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,3] 2 profile1_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,3] 2 profile1_node34_cert).mp (by decide +kernel))

def profile1_node35_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 10 20 41 82), lower := (rows 1 2 5 10 20 41 64), losses := [{ target := 0, region := (rows 0 127 4 127 20 32 84), good := (rows 10 10 94 10 94 42 74) }] }

theorem profile1_node35 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,9] 2 profile1_node35_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,9] 2 profile1_node35_cert).mp (by decide +kernel))

def profile1_node36_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 10 20 42 81), lower := (rows 1 2 5 10 20 42 64), losses := [{ target := 0, region := (rows 0 127 4 127 20 127 64), good := (rows 42 42 62 42 62 42 106) }] }

theorem profile1_node36 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,10] 2 profile1_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,10] 2 profile1_node36_cert).mp (by decide +kernel))

def profile1_node37_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 10 20 49 74), lower := (rows 1 2 5 10 20 49 64), losses := [{ target := 0, region := (rows 0 127 4 127 20 32 127), good := (rows 74 74 94 74 94 122 74) }] }

theorem profile1_node37 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,17] 2 profile1_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,17] 2 profile1_node37_cert).mp (by decide +kernel))

def profile1_node38_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 10 20 50 73), lower := (rows 1 2 5 10 20 50 64), losses := [{ target := 0, region := (rows 0 127 4 127 20 52 64), good := (rows 10 10 62 10 62 58 74) }] }

theorem profile1_node38 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,18] 2 profile1_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,18] 2 profile1_node38_cert).mp (by decide +kernel))

def profile1_node39_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 10 20 56 67), lower := (rows 1 2 5 10 20 56 64), losses := [{ target := 0, region := (rows 0 127 4 127 20 52 64), good := (rows 10 10 62 10 62 58 74) },{ target := 1, region := (rows 127 0 127 8 127 40 64), good := (rows 21 21 21 61 21 61 85) }] }

theorem profile1_node39 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,24] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,24] 2 profile1_node39_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4,24] 2 profile1_node39_cert).mp (by decide +kernel))

def profile1_node33_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node33 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile1_node33_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,4] (choices 2) [3,9,10,17,18,24] profile1_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node34
  · exact profile1_node35
  · exact profile1_node36
  · exact profile1_node37
  · exact profile1_node38
  · exact profile1_node39

def profile1_node41_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 10 24 35 84), lower := (rows 1 2 5 10 24 35 64), losses := [] }

theorem profile1_node41 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,3] 2 profile1_node41_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,3] 2 profile1_node41_cert).mp (by decide +kernel))

def profile1_node42_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 10 24 37 82), lower := (rows 1 2 5 10 24 37 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 32 127), good := (rows 90 90 94 90 90 126 90) }] }

theorem profile1_node42 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,5] 2 profile1_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,5] 2 profile1_node42_cert).mp (by decide +kernel))

def profile1_node43_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 10 24 38 81), lower := (rows 1 2 5 10 24 38 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 36 64), good := (rows 26 26 62 26 26 62 90) }] }

theorem profile1_node43 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,6] 2 profile1_node43_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,6] 2 profile1_node43_cert).mp (by decide +kernel))

def profile1_node44_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 10 24 49 70), lower := (rows 1 2 5 10 24 49 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 32 68), good := (rows 26 26 94 26 26 58 90) }] }

theorem profile1_node44 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,17] 2 profile1_node44_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,17] 2 profile1_node44_cert).mp (by decide +kernel))

def profile1_node45_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 10 24 50 69), lower := (rows 1 2 5 10 24 50 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 127 64), good := (rows 58 58 62 58 58 58 122) }] }

theorem profile1_node45 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,18] 2 profile1_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,18] 2 profile1_node45_cert).mp (by decide +kernel))

def profile1_node46_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 10 24 52 67), lower := (rows 1 2 5 10 24 52 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 36 64), good := (rows 26 26 62 26 26 62 90) },{ target := 1, region := (rows 127 0 127 8 24 56 64), good := (rows 5 5 5 61 61 53 69) }] }

theorem profile1_node46 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,20] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,20] 2 profile1_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8,20] 2 profile1_node46_cert).mp (by decide +kernel))

def profile1_node40_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node40 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8] 2 (by decide) (choices 2) [3,5,6,17,18,20] profile1_node40_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2,8] (choices 2) [3,5,6,17,18,20] profile1_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node41
  · exact profile1_node42
  · exact profile1_node43
  · exact profile1_node44
  · exact profile1_node45
  · exact profile1_node46

def profile1_node18_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node18 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2] 2 (by decide) (choices 1) [1,2,4,8] profile1_node18_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,2] (choices 1) [1,2,4,8] profile1_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node19
  · exact profile1_node26
  · exact profile1_node33
  · exact profile1_node40

def profile1_node49_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 12 17 42 82), lower := (rows 1 2 5 12 17 42 64), losses := [{ target := 0, region := (rows 0 127 4 12 16 44 80), good := (rows 2 2 46 46 82 42 66) }] }

theorem profile1_node49 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,1,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,1,10] 2 profile1_node49_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,1,10] 2 profile1_node49_cert).mp (by decide +kernel))

def profile1_node50_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 12 17 50 74), lower := (rows 1 2 5 12 17 50 64), losses := [{ target := 0, region := (rows 0 127 4 12 16 48 76), good := (rows 2 2 78 78 50 50 66) }] }

theorem profile1_node50 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,1,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,1,18] 2 profile1_node50_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,1,18] 2 profile1_node50_cert).mp (by decide +kernel))

def profile1_node48_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node48 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,1] 2 (by decide) (choices 2) [10,18] profile1_node48_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,1] (choices 2) [10,18] profile1_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node49
  · exact profile1_node50

def profile1_node52_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 12 18 35 88), lower := (rows 1 2 5 12 18 35 64), losses := [] }

theorem profile1_node52 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,3] 2 profile1_node52_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,3] 2 profile1_node52_cert).mp (by decide +kernel))

def profile1_node53_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 12 18 41 82), lower := (rows 1 2 5 12 18 41 64), losses := [{ target := 0, region := (rows 0 127 4 12 127 32 127), good := (rows 82 82 94 94 82 122 82) }] }

theorem profile1_node53 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,9] 2 profile1_node53_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,9] 2 profile1_node53_cert).mp (by decide +kernel))

def profile1_node54_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 12 18 42 81), lower := (rows 1 2 5 12 18 42 64), losses := [{ target := 0, region := (rows 0 127 4 12 127 44 64), good := (rows 18 18 62 62 18 58 82) }] }

theorem profile1_node54 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,10] 2 profile1_node54_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,10] 2 profile1_node54_cert).mp (by decide +kernel))

def profile1_node55_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 12 18 49 74), lower := (rows 1 2 5 12 18 49 64), losses := [{ target := 0, region := (rows 0 127 4 12 127 32 76), good := (rows 18 18 94 94 18 50 82) }] }

theorem profile1_node55 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,17] 2 profile1_node55_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,17] 2 profile1_node55_cert).mp (by decide +kernel))

def profile1_node56_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 12 18 50 73), lower := (rows 1 2 5 12 18 50 64), losses := [{ target := 0, region := (rows 0 127 4 12 127 127 64), good := (rows 50 50 62 62 50 50 114) }] }

theorem profile1_node56 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,18] 2 profile1_node56_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,18] 2 profile1_node56_cert).mp (by decide +kernel))

def profile1_node57_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 12 18 56 67), lower := (rows 1 2 5 12 18 56 64), losses := [{ target := 0, region := (rows 0 127 4 12 127 44 64), good := (rows 18 18 62 62 18 58 82) },{ target := 1, region := (rows 127 0 127 127 16 48 64), good := (rows 13 13 13 13 61 61 77) }] }

theorem profile1_node57 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,24] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,24] 2 profile1_node57_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2,24] 2 profile1_node57_cert).mp (by decide +kernel))

def profile1_node51_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node51 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile1_node51_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,2] (choices 2) [3,9,10,17,18,24] profile1_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node52
  · exact profile1_node53
  · exact profile1_node54
  · exact profile1_node55
  · exact profile1_node56
  · exact profile1_node57

def profile1_node59_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 12 24 35 82), lower := (rows 1 2 5 12 24 35 64), losses := [] }

theorem profile1_node59 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,8,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,8,3] 2 profile1_node59_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,8,3] 2 profile1_node59_cert).mp (by decide +kernel))

def profile1_node60_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 12 24 50 67), lower := (rows 1 2 5 12 24 50 64), losses := [{ target := 0, region := (rows 0 127 4 12 28 60 64), good := (rows 2 2 62 62 58 50 66) }] }

theorem profile1_node60 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,8,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,8,18] 2 profile1_node60_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,8,18] 2 profile1_node60_cert).mp (by decide +kernel))

def profile1_node58_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node58 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,8] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,8] 2 (by decide) (choices 2) [3,18] profile1_node58_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4,8] (choices 2) [3,18] profile1_node58_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node59
  · exact profile1_node60

def profile1_node47_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node47 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4] 2 (by decide) (choices 1) [1,2,8] profile1_node47_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,4] (choices 1) [1,2,8] profile1_node47_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node48
  · exact profile1_node51
  · exact profile1_node58

def profile1_node63_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 24 17 38 74), lower := (rows 1 2 5 24 17 38 64), losses := [{ target := 0, region := (rows 0 127 4 24 16 36 88), good := (rows 2 2 38 90 90 38 66) }] }

theorem profile1_node63 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,1,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,1,6] 2 profile1_node63_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,1,6] 2 profile1_node63_cert).mp (by decide +kernel))

def profile1_node64_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 5 24 17 42 70), lower := (rows 1 2 5 24 17 42 64), losses := [{ target := 0, region := (rows 0 127 4 24 16 56 68), good := (rows 2 2 70 58 58 42 66) }] }

theorem profile1_node64 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,1,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,1,10] 2 profile1_node64_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,1,10] 2 profile1_node64_cert).mp (by decide +kernel))

def profile1_node62_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node62 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,1] 2 (by decide) (choices 2) [6,10] profile1_node62_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,1] (choices 2) [6,10] profile1_node62_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node63
  · exact profile1_node64

def profile1_node66_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 24 18 35 76), lower := (rows 1 2 5 24 18 35 64), losses := [] }

theorem profile1_node66 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,3] 2 profile1_node66_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,3] 2 profile1_node66_cert).mp (by decide +kernel))

def profile1_node67_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 24 18 37 74), lower := (rows 1 2 5 24 18 37 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 32 127), good := (rows 90 90 94 90 90 126 90) }] }

theorem profile1_node67 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,5] 2 profile1_node67_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,5] 2 profile1_node67_cert).mp (by decide +kernel))

def profile1_node68_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 24 18 38 73), lower := (rows 1 2 5 24 18 38 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 36 64), good := (rows 26 26 62 26 26 62 90) }] }

theorem profile1_node68 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,6] 2 profile1_node68_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,6] 2 profile1_node68_cert).mp (by decide +kernel))

def profile1_node69_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 5 24 18 41 70), lower := (rows 1 2 5 24 18 41 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 32 68), good := (rows 26 26 94 26 26 58 90) }] }

theorem profile1_node69 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,9] 2 profile1_node69_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,9] 2 profile1_node69_cert).mp (by decide +kernel))

def profile1_node70_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 24 18 42 69), lower := (rows 1 2 5 24 18 42 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 127 64), good := (rows 58 58 62 58 58 58 122) }] }

theorem profile1_node70 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,10] 2 profile1_node70_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,10] 2 profile1_node70_cert).mp (by decide +kernel))

def profile1_node71_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 24 18 44 67), lower := (rows 1 2 5 24 18 44 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 36 64), good := (rows 26 26 62 26 26 62 90) },{ target := 1, region := (rows 127 0 127 24 16 56 64), good := (rows 5 5 5 61 61 45 69) }] }

theorem profile1_node71 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,12] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,12] 2 profile1_node71_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2,12] 2 profile1_node71_cert).mp (by decide +kernel))

def profile1_node65_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node65 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile1_node65_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,2] (choices 2) [3,5,6,9,10,12] profile1_node65_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node66
  · exact profile1_node67
  · exact profile1_node68
  · exact profile1_node69
  · exact profile1_node70
  · exact profile1_node71

def profile1_node73_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 24 20 35 74), lower := (rows 1 2 5 24 20 35 64), losses := [] }

theorem profile1_node73 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,4,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,4,3] 2 profile1_node73_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,4,3] 2 profile1_node73_cert).mp (by decide +kernel))

def profile1_node74_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 24 20 42 67), lower := (rows 1 2 5 24 20 42 64), losses := [{ target := 0, region := (rows 0 127 4 28 20 60 64), good := (rows 2 2 62 58 62 42 66) }] }

theorem profile1_node74 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,4,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,4,10] 2 profile1_node74_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,4,10] 2 profile1_node74_cert).mp (by decide +kernel))

def profile1_node72_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node72 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,4] 2 (by decide) (choices 2) [3,10] profile1_node72_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,4] (choices 2) [3,10] profile1_node72_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node73
  · exact profile1_node74

def profile1_node76_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 24 24 35 70), lower := (rows 1 2 5 24 24 35 64), losses := [] }

theorem profile1_node76 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,8,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,8,3] 2 profile1_node76_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,8,3] 2 profile1_node76_cert).mp (by decide +kernel))

def profile1_node77_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 5 24 24 38 67), lower := (rows 1 2 5 24 24 38 64), losses := [{ target := 0, region := (rows 0 127 4 127 127 36 64), good := (rows 26 26 62 26 26 62 90) }] }

theorem profile1_node77 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,8,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,8,6] 2 profile1_node77_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,8,6] 2 profile1_node77_cert).mp (by decide +kernel))

def profile1_node75_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node75 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,8] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,8] 2 (by decide) (choices 2) [3,6] profile1_node75_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16,8] (choices 2) [3,6] profile1_node75_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node76
  · exact profile1_node77

def profile1_node61_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node61 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16] 2 (by decide) (choices 1) [1,2,4,8] profile1_node61_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1,16] (choices 1) [1,2,4,8] profile1_node61_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node62
  · exact profile1_node65
  · exact profile1_node72
  · exact profile1_node75

def profile1_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node3 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1] 2 (by decide) (choices 1) [1,2,4,16] profile1_node3_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,1] (choices 1) [1,2,4,16] profile1_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node4
  · exact profile1_node18
  · exact profile1_node47
  · exact profile1_node61

def profile1_node81_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 9 17 38 88), lower := (rows 1 2 6 9 17 38 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 64), good := (rows 38 38 38 46 54 38 102) }] }

theorem profile1_node81 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,6] 2 profile1_node81_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,6] 2 profile1_node81_cert).mp (by decide +kernel))

def profile1_node82_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 6 9 17 42 84), lower := (rows 1 2 6 9 17 42 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 40 80), good := (rows 6 6 6 46 86 46 70) }] }

theorem profile1_node82 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,10] 2 profile1_node82_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,10] 2 profile1_node82_cert).mp (by decide +kernel))

def profile1_node83_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 9 17 44 82), lower := (rows 1 2 6 9 17 44 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 40 80), good := (rows 6 6 6 46 86 46 70) }] }

theorem profile1_node83 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,12] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,12] 2 profile1_node83_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,12] 2 profile1_node83_cert).mp (by decide +kernel))

def profile1_node84_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 6 9 17 50 76), lower := (rows 1 2 6 9 17 50 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 48 72), good := (rows 6 6 6 78 54 54 70) }] }

theorem profile1_node84 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,18] 2 profile1_node84_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,18] 2 profile1_node84_cert).mp (by decide +kernel))

def profile1_node85_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 9 17 52 74), lower := (rows 1 2 6 9 17 52 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 48 72), good := (rows 6 6 6 78 54 54 70) }] }

theorem profile1_node85 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,20] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,20] 2 profile1_node85_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,20] 2 profile1_node85_cert).mp (by decide +kernel))

def profile1_node86_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 1 2), upper := (rows 1 2 6 9 17 56 70), lower := (rows 1 2 6 9 17 56 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 32 127), good := (rows 70 70 70 78 86 126 70) },{ target := 1, region := (rows 127 0 4 127 127 127 64), good := (rows 57 57 61 57 57 57 121) }] }

theorem profile1_node86 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,24] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,24] 2 profile1_node86_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1,24] 2 profile1_node86_cert).mp (by decide +kernel))

def profile1_node80_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node80 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1] 2 (by decide) (choices 2) [6,10,12,18,20,24] profile1_node80_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,1] (choices 2) [6,10,12,18,20,24] profile1_node80_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node81
  · exact profile1_node82
  · exact profile1_node83
  · exact profile1_node84
  · exact profile1_node85
  · exact profile1_node86

def profile1_node88_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 9 18 37 88), lower := (rows 1 2 6 9 18 37 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 32 72), good := (rows 22 22 22 94 22 54 86) }] }

theorem profile1_node88 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,5] 2 profile1_node88_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,5] 2 profile1_node88_cert).mp (by decide +kernel))

def profile1_node89_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 9 18 41 84), lower := (rows 1 2 6 9 18 41 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 32 127), good := (rows 86 86 86 94 86 126 86) }] }

theorem profile1_node89 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,9] 2 profile1_node89_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,9] 2 profile1_node89_cert).mp (by decide +kernel))

def profile1_node90_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 9 18 44 81), lower := (rows 1 2 6 9 18 44 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 40 64), good := (rows 22 22 22 62 22 62 86) },{ target := 1, region := (rows 127 0 4 127 16 36 80), good := (rows 9 9 45 9 89 45 73) }] }

theorem profile1_node90 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,12] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,12] 2 profile1_node90_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,12] 2 profile1_node90_cert).mp (by decide +kernel))

def profile1_node91_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 9 18 49 76), lower := (rows 1 2 6 9 18 49 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 32 72), good := (rows 22 22 22 94 22 54 86) }] }

theorem profile1_node91 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,17] 2 profile1_node91_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,17] 2 profile1_node91_cert).mp (by decide +kernel))

def profile1_node92_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 1), upper := (rows 1 2 6 9 18 52 73), lower := (rows 1 2 6 9 18 52 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 127 64), good := (rows 54 54 54 62 54 54 118) },{ target := 1, region := (rows 127 0 4 127 16 32 127), good := (rows 73 73 77 73 89 125 73) }] }

theorem profile1_node92 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,20] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,20] 2 profile1_node92_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,20] 2 profile1_node92_cert).mp (by decide +kernel))

def profile1_node93_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 9 18 56 69), lower := (rows 1 2 6 9 18 56 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 40 64), good := (rows 22 22 22 62 22 62 86) },{ target := 1, region := (rows 127 0 4 127 16 48 68), good := (rows 9 9 77 9 57 57 73) }] }

theorem profile1_node93 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,24] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,24] 2 profile1_node93_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2,24] 2 profile1_node93_cert).mp (by decide +kernel))

def profile1_node87_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node87 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2] 2 (by decide) (choices 2) [5,9,12,17,20,24] profile1_node87_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,2] (choices 2) [5,9,12,17,20,24] profile1_node87_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node88
  · exact profile1_node89
  · exact profile1_node90
  · exact profile1_node91
  · exact profile1_node92
  · exact profile1_node93

def profile1_node95_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 9 20 35 88), lower := (rows 1 2 6 9 20 35 64), losses := [] }

theorem profile1_node95 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,3] 2 profile1_node95_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,3] 2 profile1_node95_cert).mp (by decide +kernel))

def profile1_node96_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 9 20 41 82), lower := (rows 1 2 6 9 20 41 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 32 127), good := (rows 86 86 86 94 86 126 86) }] }

theorem profile1_node96 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,9] 2 profile1_node96_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,9] 2 profile1_node96_cert).mp (by decide +kernel))

def profile1_node97_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 9 20 42 81), lower := (rows 1 2 6 9 20 42 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 40 64), good := (rows 22 22 22 62 22 62 86) }] }

theorem profile1_node97 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,10] 2 profile1_node97_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,10] 2 profile1_node97_cert).mp (by decide +kernel))

def profile1_node98_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 9 20 49 74), lower := (rows 1 2 6 9 20 49 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 32 72), good := (rows 22 22 22 94 22 54 86) }] }

theorem profile1_node98 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,17] 2 profile1_node98_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,17] 2 profile1_node98_cert).mp (by decide +kernel))

def profile1_node99_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 9 20 50 73), lower := (rows 1 2 6 9 20 50 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 127 64), good := (rows 54 54 54 62 54 54 118) }] }

theorem profile1_node99 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,18] 2 profile1_node99_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,18] 2 profile1_node99_cert).mp (by decide +kernel))

def profile1_node100_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 9 20 56 67), lower := (rows 1 2 6 9 20 56 64), losses := [{ target := 0, region := (rows 0 127 127 8 127 40 64), good := (rows 22 22 22 62 22 62 86) },{ target := 1, region := (rows 127 0 4 127 20 52 64), good := (rows 9 9 61 9 61 57 73) }] }

theorem profile1_node100 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,24] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,24] 2 profile1_node100_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4,24] 2 profile1_node100_cert).mp (by decide +kernel))

def profile1_node94_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node94 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile1_node94_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,4] (choices 2) [3,9,10,17,18,24] profile1_node94_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node95
  · exact profile1_node96
  · exact profile1_node97
  · exact profile1_node98
  · exact profile1_node99
  · exact profile1_node100

def profile1_node102_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 9 24 35 84), lower := (rows 1 2 6 9 24 35 64), losses := [] }

theorem profile1_node102 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,3] 2 profile1_node102_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,3] 2 profile1_node102_cert).mp (by decide +kernel))

def profile1_node103_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 9 24 37 82), lower := (rows 1 2 6 9 24 37 64), losses := [{ target := 0, region := (rows 0 127 127 8 24 32 88), good := (rows 6 6 6 94 94 38 70) }] }

theorem profile1_node103 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,5] 2 profile1_node103_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,5] 2 profile1_node103_cert).mp (by decide +kernel))

def profile1_node104_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 9 24 38 81), lower := (rows 1 2 6 9 24 38 64), losses := [{ target := 0, region := (rows 0 127 127 8 24 127 64), good := (rows 38 38 38 62 62 38 102) }] }

theorem profile1_node104 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,6] 2 profile1_node104_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,6] 2 profile1_node104_cert).mp (by decide +kernel))

def profile1_node105_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 9 24 49 70), lower := (rows 1 2 6 9 24 49 64), losses := [{ target := 0, region := (rows 0 127 127 8 24 32 127), good := (rows 70 70 70 94 94 118 70) }] }

theorem profile1_node105 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,17] 2 profile1_node105_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,17] 2 profile1_node105_cert).mp (by decide +kernel))

def profile1_node106_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 9 24 50 69), lower := (rows 1 2 6 9 24 50 64), losses := [{ target := 0, region := (rows 0 127 127 8 24 56 64), good := (rows 6 6 6 62 62 54 70) }] }

theorem profile1_node106 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,18] 2 profile1_node106_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,18] 2 profile1_node106_cert).mp (by decide +kernel))

def profile1_node107_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 9 24 52 67), lower := (rows 1 2 6 9 24 52 64), losses := [{ target := 0, region := (rows 0 127 127 8 24 56 64), good := (rows 6 6 6 62 62 54 70) },{ target := 1, region := (rows 127 0 4 127 127 36 64), good := (rows 25 25 61 25 25 61 89) }] }

theorem profile1_node107 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,20] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,20] 2 profile1_node107_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8,20] 2 profile1_node107_cert).mp (by decide +kernel))

def profile1_node101_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node101 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8] 2 (by decide) (choices 2) [3,5,6,17,18,20] profile1_node101_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1,8] (choices 2) [3,5,6,17,18,20] profile1_node101_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node102
  · exact profile1_node103
  · exact profile1_node104
  · exact profile1_node105
  · exact profile1_node106
  · exact profile1_node107

def profile1_node79_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node79 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1] 2 (by decide) (choices 1) [1,2,4,8] profile1_node79_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,1] (choices 1) [1,2,4,8] profile1_node79_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node80
  · exact profile1_node87
  · exact profile1_node94
  · exact profile1_node101

def profile1_node110_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 10 17 37 88), lower := (rows 1 2 6 10 17 37 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 80), good := (rows 14 14 14 14 94 46 78) }] }

theorem profile1_node110 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,5] 2 profile1_node110_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,5] 2 profile1_node110_cert).mp (by decide +kernel))

def profile1_node111_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 10 17 41 84), lower := (rows 1 2 6 10 17 41 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 80), good := (rows 14 14 14 14 94 46 78) }] }

theorem profile1_node111 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,9] 2 profile1_node111_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,9] 2 profile1_node111_cert).mp (by decide +kernel))

def profile1_node112_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 1), upper := (rows 1 2 6 10 17 44 81), lower := (rows 1 2 6 10 17 44 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) },{ target := 1, region := (rows 127 0 4 8 127 32 127), good := (rows 81 81 85 89 81 125 81) }] }

theorem profile1_node112 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,12] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,12] 2 profile1_node112_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,12] 2 profile1_node112_cert).mp (by decide +kernel))

def profile1_node113_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 10 17 49 76), lower := (rows 1 2 6 10 17 49 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 126 78) }] }

theorem profile1_node113 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,17] 2 profile1_node113_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,17] 2 profile1_node113_cert).mp (by decide +kernel))

def profile1_node114_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 10 17 52 73), lower := (rows 1 2 6 10 17 52 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 48 64), good := (rows 14 14 14 14 62 62 78) },{ target := 1, region := (rows 127 0 4 8 127 36 72), good := (rows 17 17 53 89 17 53 81) }] }

theorem profile1_node114 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,20] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,20] 2 profile1_node114_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,20] 2 profile1_node114_cert).mp (by decide +kernel))

def profile1_node115_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 10 17 56 69), lower := (rows 1 2 6 10 17 56 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 48 64), good := (rows 14 14 14 14 62 62 78) },{ target := 1, region := (rows 127 0 4 8 127 40 68), good := (rows 17 17 85 57 17 57 81) }] }

theorem profile1_node115 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,24] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,24] 2 profile1_node115_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1,24] 2 profile1_node115_cert).mp (by decide +kernel))

def profile1_node109_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node109 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1] 2 (by decide) (choices 2) [5,9,12,17,20,24] profile1_node109_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,1] (choices 2) [5,9,12,17,20,24] profile1_node109_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node110
  · exact profile1_node111
  · exact profile1_node112
  · exact profile1_node113
  · exact profile1_node114
  · exact profile1_node115

def profile1_node117_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 10 20 41 81), lower := (rows 1 2 6 10 20 41 64), losses := [{ target := 1, region := (rows 127 0 4 8 20 40 84), good := (rows 1 1 85 41 85 41 65) }] }

theorem profile1_node117 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,4,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,4,9] 2 profile1_node117_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,4,9] 2 profile1_node117_cert).mp (by decide +kernel))

def profile1_node118_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 10 20 49 73), lower := (rows 1 2 6 10 20 49 64), losses := [{ target := 1, region := (rows 127 0 4 8 20 52 72), good := (rows 1 1 53 73 53 49 65) }] }

theorem profile1_node118 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,4,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,4,17] 2 profile1_node118_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,4,17] 2 profile1_node118_cert).mp (by decide +kernel))

def profile1_node116_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node116 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,4] 2 (by decide) (choices 2) [9,17] profile1_node116_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,4] (choices 2) [9,17] profile1_node116_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node117
  · exact profile1_node118

def profile1_node120_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 10 24 37 81), lower := (rows 1 2 6 10 24 37 64), losses := [{ target := 1, region := (rows 127 0 4 8 24 36 88), good := (rows 1 1 37 89 89 37 65) }] }

theorem profile1_node120 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,8,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,8,5] 2 profile1_node120_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,8,5] 2 profile1_node120_cert).mp (by decide +kernel))

def profile1_node121_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 10 24 49 69), lower := (rows 1 2 6 10 24 49 64), losses := [{ target := 1, region := (rows 127 0 4 8 24 56 68), good := (rows 1 1 69 57 57 49 65) }] }

theorem profile1_node121 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,8,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,8,17] 2 profile1_node121_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,8,17] 2 profile1_node121_cert).mp (by decide +kernel))

def profile1_node119_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node119 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,8] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,8] 2 (by decide) (choices 2) [5,17] profile1_node119_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2,8] (choices 2) [5,17] profile1_node119_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node120
  · exact profile1_node121

def profile1_node108_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node108 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2] 2 (by decide) (choices 1) [1,4,8] profile1_node108_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,2] (choices 1) [1,4,8] profile1_node108_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node109
  · exact profile1_node116
  · exact profile1_node119

def profile1_node124_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 12 17 35 88), lower := (rows 1 2 6 12 17 35 64), losses := [] }

theorem profile1_node124 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,3] 2 profile1_node124_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,3] 2 profile1_node124_cert).mp (by decide +kernel))

def profile1_node125_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 12 17 41 82), lower := (rows 1 2 6 12 17 41 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 80), good := (rows 14 14 14 14 94 46 78) }] }

theorem profile1_node125 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,9] 2 profile1_node125_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,9] 2 profile1_node125_cert).mp (by decide +kernel))

def profile1_node126_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 12 17 42 81), lower := (rows 1 2 6 12 17 42 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) }] }

theorem profile1_node126 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,10] 2 profile1_node126_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,10] 2 profile1_node126_cert).mp (by decide +kernel))

def profile1_node127_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 12 17 49 74), lower := (rows 1 2 6 12 17 49 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 126 78) }] }

theorem profile1_node127 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,17] 2 profile1_node127_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,17] 2 profile1_node127_cert).mp (by decide +kernel))

def profile1_node128_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 12 17 50 73), lower := (rows 1 2 6 12 17 50 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 48 64), good := (rows 14 14 14 14 62 62 78) }] }

theorem profile1_node128 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,18] 2 profile1_node128_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,18] 2 profile1_node128_cert).mp (by decide +kernel))

def profile1_node129_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 12 17 56 67), lower := (rows 1 2 6 12 17 56 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 48 64), good := (rows 14 14 14 14 62 62 78) },{ target := 1, region := (rows 127 0 4 12 127 44 64), good := (rows 17 17 61 61 17 57 81) }] }

theorem profile1_node129 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,24] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,24] 2 profile1_node129_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1,24] 2 profile1_node129_cert).mp (by decide +kernel))

def profile1_node123_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node123 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile1_node123_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,1] (choices 2) [3,9,10,17,18,24] profile1_node123_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node124
  · exact profile1_node125
  · exact profile1_node126
  · exact profile1_node127
  · exact profile1_node128
  · exact profile1_node129

def profile1_node131_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 12 18 41 81), lower := (rows 1 2 6 12 18 41 64), losses := [{ target := 1, region := (rows 127 0 4 12 16 44 80), good := (rows 1 1 45 45 81 41 65) }] }

theorem profile1_node131 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,2,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,2,9] 2 profile1_node131_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,2,9] 2 profile1_node131_cert).mp (by decide +kernel))

def profile1_node132_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 12 18 49 73), lower := (rows 1 2 6 12 18 49 64), losses := [{ target := 1, region := (rows 127 0 4 12 16 48 76), good := (rows 1 1 77 77 49 49 65) }] }

theorem profile1_node132 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,2,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,2,17] 2 profile1_node132_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,2,17] 2 profile1_node132_cert).mp (by decide +kernel))

def profile1_node130_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node130 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,2] 2 (by decide) (choices 2) [9,17] profile1_node130_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,2] (choices 2) [9,17] profile1_node130_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node131
  · exact profile1_node132

def profile1_node134_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 12 24 35 81), lower := (rows 1 2 6 12 24 35 64), losses := [] }

theorem profile1_node134 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,8,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,8,3] 2 profile1_node134_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,8,3] 2 profile1_node134_cert).mp (by decide +kernel))

def profile1_node135_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 12 24 49 67), lower := (rows 1 2 6 12 24 49 64), losses := [{ target := 1, region := (rows 127 0 4 12 28 60 64), good := (rows 1 1 61 61 57 49 65) }] }

theorem profile1_node135 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,8,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,8,17] 2 profile1_node135_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,8,17] 2 profile1_node135_cert).mp (by decide +kernel))

def profile1_node133_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node133 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,8] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,8] 2 (by decide) (choices 2) [3,17] profile1_node133_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4,8] (choices 2) [3,17] profile1_node133_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node134
  · exact profile1_node135

def profile1_node122_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node122 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4] 2 (by decide) (choices 1) [1,2,8] profile1_node122_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,4] (choices 1) [1,2,8] profile1_node122_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node123
  · exact profile1_node130
  · exact profile1_node133

def profile1_node138_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 24 17 35 76), lower := (rows 1 2 6 24 17 35 64), losses := [] }

theorem profile1_node138 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,3] 2 profile1_node138_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,3] 2 profile1_node138_cert).mp (by decide +kernel))

def profile1_node139_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 24 17 37 74), lower := (rows 1 2 6 24 17 37 64), losses := [{ target := 0, region := (rows 0 127 127 24 16 32 88), good := (rows 6 6 6 94 94 38 70) }] }

theorem profile1_node139 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,5] 2 profile1_node139_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,5] 2 profile1_node139_cert).mp (by decide +kernel))

def profile1_node140_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 24 17 38 73), lower := (rows 1 2 6 24 17 38 64), losses := [{ target := 0, region := (rows 0 127 127 24 16 127 64), good := (rows 38 38 38 62 62 38 102) }] }

theorem profile1_node140 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,6] 2 profile1_node140_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,6] 2 profile1_node140_cert).mp (by decide +kernel))

def profile1_node141_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 6 24 17 41 70), lower := (rows 1 2 6 24 17 41 64), losses := [{ target := 0, region := (rows 0 127 127 24 16 32 127), good := (rows 70 70 70 94 94 110 70) }] }

theorem profile1_node141 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,9] 2 profile1_node141_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,9] 2 profile1_node141_cert).mp (by decide +kernel))

def profile1_node142_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 24 17 42 69), lower := (rows 1 2 6 24 17 42 64), losses := [{ target := 0, region := (rows 0 127 127 24 16 56 64), good := (rows 6 6 6 62 62 46 70) }] }

theorem profile1_node142 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,10] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,10] 2 profile1_node142_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,10] 2 profile1_node142_cert).mp (by decide +kernel))

def profile1_node143_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 24 17 44 67), lower := (rows 1 2 6 24 17 44 64), losses := [{ target := 0, region := (rows 0 127 127 24 16 56 64), good := (rows 6 6 6 62 62 46 70) },{ target := 1, region := (rows 127 0 4 127 127 36 64), good := (rows 25 25 61 25 25 61 89) }] }

theorem profile1_node143 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,12] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,12] 2 profile1_node143_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1,12] 2 profile1_node143_cert).mp (by decide +kernel))

def profile1_node137_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node137 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1] 2 (by decide) (choices 2) [3,5,6,9,10,12] profile1_node137_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,1] (choices 2) [3,5,6,9,10,12] profile1_node137_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node138
  · exact profile1_node139
  · exact profile1_node140
  · exact profile1_node141
  · exact profile1_node142
  · exact profile1_node143

def profile1_node145_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 24 18 37 73), lower := (rows 1 2 6 24 18 37 64), losses := [{ target := 1, region := (rows 127 0 4 24 16 36 88), good := (rows 1 1 37 89 89 37 65) }] }

theorem profile1_node145 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,2,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,2,5] 2 profile1_node145_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,2,5] 2 profile1_node145_cert).mp (by decide +kernel))

def profile1_node146_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 6 24 18 41 69), lower := (rows 1 2 6 24 18 41 64), losses := [{ target := 1, region := (rows 127 0 4 24 16 56 68), good := (rows 1 1 69 57 57 41 65) }] }

theorem profile1_node146 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,2,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,2,9] 2 profile1_node146_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,2,9] 2 profile1_node146_cert).mp (by decide +kernel))

def profile1_node144_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node144 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,2] 2 (by decide) (choices 2) [5,9] profile1_node144_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,2] (choices 2) [5,9] profile1_node144_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node145
  · exact profile1_node146

def profile1_node148_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 24 20 35 73), lower := (rows 1 2 6 24 20 35 64), losses := [] }

theorem profile1_node148 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,4,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,4,3] 2 profile1_node148_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,4,3] 2 profile1_node148_cert).mp (by decide +kernel))

def profile1_node149_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 24 20 41 67), lower := (rows 1 2 6 24 20 41 64), losses := [{ target := 1, region := (rows 127 0 4 28 20 60 64), good := (rows 1 1 61 57 61 41 65) }] }

theorem profile1_node149 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,4,9] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,4,9] 2 profile1_node149_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,4,9] 2 profile1_node149_cert).mp (by decide +kernel))

def profile1_node147_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node147 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,4] 2 (by decide) (choices 2) [3,9] profile1_node147_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,4] (choices 2) [3,9] profile1_node147_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node148
  · exact profile1_node149

def profile1_node151_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 24 24 35 69), lower := (rows 1 2 6 24 24 35 64), losses := [] }

theorem profile1_node151 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,8,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,8,3] 2 profile1_node151_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,8,3] 2 profile1_node151_cert).mp (by decide +kernel))

def profile1_node152_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 6 24 24 37 67), lower := (rows 1 2 6 24 24 37 64), losses := [{ target := 1, region := (rows 127 0 4 127 127 36 64), good := (rows 25 25 61 25 25 61 89) }] }

theorem profile1_node152 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,8,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,8,5] 2 profile1_node152_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,8,5] 2 profile1_node152_cert).mp (by decide +kernel))

def profile1_node150_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node150 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,8] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,8] 2 (by decide) (choices 2) [3,5] profile1_node150_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16,8] (choices 2) [3,5] profile1_node150_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node151
  · exact profile1_node152

def profile1_node136_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node136 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16] 2 (by decide) (choices 1) [1,2,4,8] profile1_node136_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2,16] (choices 1) [1,2,4,8] profile1_node136_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node137
  · exact profile1_node144
  · exact profile1_node147
  · exact profile1_node150

def profile1_node78_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node78 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2] 2 (by decide) (choices 1) [1,2,4,16] profile1_node78_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,2] (choices 1) [1,2,4,16] profile1_node78_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node79
  · exact profile1_node108
  · exact profile1_node122
  · exact profile1_node136

def profile1_node156_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 12 9 17 38 82), lower := (rows 1 2 12 9 17 38 64), losses := [{ target := 0, region := (rows 0 127 12 8 16 44 80), good := (rows 2 2 46 46 82 38 66) }] }

theorem profile1_node156 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,1,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,1,6] 2 profile1_node156_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,1,6] 2 profile1_node156_cert).mp (by decide +kernel))

def profile1_node157_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 2), upper := (rows 1 2 12 9 17 50 70), lower := (rows 1 2 12 9 17 50 64), losses := [{ target := 0, region := (rows 0 127 12 8 16 48 76), good := (rows 2 2 78 78 50 50 66) }] }

theorem profile1_node157 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,1,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,1,18] 2 profile1_node157_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,1,18] 2 profile1_node157_cert).mp (by decide +kernel))

def profile1_node155_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node155 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,1] 2 (by decide) (choices 2) [6,18] profile1_node155_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,1] (choices 2) [6,18] profile1_node155_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node156
  · exact profile1_node157

def profile1_node159_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 9 18 35 84), lower := (rows 1 2 12 9 18 35 64), losses := [] }

theorem profile1_node159 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,3] 2 profile1_node159_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,3] 2 profile1_node159_cert).mp (by decide +kernel))

def profile1_node160_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 12 9 18 37 82), lower := (rows 1 2 12 9 18 37 64), losses := [{ target := 0, region := (rows 0 127 12 8 127 32 127), good := (rows 82 82 94 94 82 118 82) }] }

theorem profile1_node160 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,5] 2 profile1_node160_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,5] 2 profile1_node160_cert).mp (by decide +kernel))

def profile1_node161_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 9 18 38 81), lower := (rows 1 2 12 9 18 38 64), losses := [{ target := 0, region := (rows 0 127 12 8 127 44 64), good := (rows 18 18 62 62 18 54 82) }] }

theorem profile1_node161 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,6] 2 profile1_node161_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,6] 2 profile1_node161_cert).mp (by decide +kernel))

def profile1_node162_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 12 9 18 49 70), lower := (rows 1 2 12 9 18 49 64), losses := [{ target := 0, region := (rows 0 127 12 8 127 32 76), good := (rows 18 18 94 94 18 50 82) }] }

theorem profile1_node162 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,17] 2 profile1_node162_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,17] 2 profile1_node162_cert).mp (by decide +kernel))

def profile1_node163_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 9 18 50 69), lower := (rows 1 2 12 9 18 50 64), losses := [{ target := 0, region := (rows 0 127 12 8 127 127 64), good := (rows 50 50 62 62 50 50 114) }] }

theorem profile1_node163 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,18] 2 profile1_node163_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,18] 2 profile1_node163_cert).mp (by decide +kernel))

def profile1_node164_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 9 18 52 67), lower := (rows 1 2 12 9 18 52 64), losses := [{ target := 0, region := (rows 0 127 12 8 127 44 64), good := (rows 18 18 62 62 18 54 82) },{ target := 1, region := (rows 127 0 127 127 16 48 64), good := (rows 13 13 13 13 61 61 77) }] }

theorem profile1_node164 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,20] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,20] 2 profile1_node164_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2,20] 2 profile1_node164_cert).mp (by decide +kernel))

def profile1_node158_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node158 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2] 2 (by decide) (choices 2) [3,5,6,17,18,20] profile1_node158_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,2] (choices 2) [3,5,6,17,18,20] profile1_node158_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node159
  · exact profile1_node160
  · exact profile1_node161
  · exact profile1_node162
  · exact profile1_node163
  · exact profile1_node164

def profile1_node166_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 9 20 35 82), lower := (rows 1 2 12 9 20 35 64), losses := [] }

theorem profile1_node166 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,4,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,4,3] 2 profile1_node166_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,4,3] 2 profile1_node166_cert).mp (by decide +kernel))

def profile1_node167_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 9 20 50 67), lower := (rows 1 2 12 9 20 50 64), losses := [{ target := 0, region := (rows 0 127 12 8 28 60 64), good := (rows 2 2 62 62 54 50 66) }] }

theorem profile1_node167 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,4,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,4,18] 2 profile1_node167_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,4,18] 2 profile1_node167_cert).mp (by decide +kernel))

def profile1_node165_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node165 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,4] 2 (by decide) (choices 2) [3,18] profile1_node165_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1,4] (choices 2) [3,18] profile1_node165_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node166
  · exact profile1_node167

def profile1_node154_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node154 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1] 2 (by decide) (choices 1) [1,2,4] profile1_node154_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,1] (choices 1) [1,2,4] profile1_node154_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node155
  · exact profile1_node158
  · exact profile1_node165

def profile1_node170_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 10 17 35 84), lower := (rows 1 2 12 10 17 35 64), losses := [] }

theorem profile1_node170 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,3] 2 profile1_node170_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,3] 2 profile1_node170_cert).mp (by decide +kernel))

def profile1_node171_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 12 10 17 37 82), lower := (rows 1 2 12 10 17 37 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 80), good := (rows 14 14 14 14 94 46 78) }] }

theorem profile1_node171 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,5] 2 profile1_node171_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,5] 2 profile1_node171_cert).mp (by decide +kernel))

def profile1_node172_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 10 17 38 81), lower := (rows 1 2 12 10 17 38 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 64), good := (rows 46 46 46 46 62 46 110) }] }

theorem profile1_node172 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,6] 2 profile1_node172_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,6] 2 profile1_node172_cert).mp (by decide +kernel))

def profile1_node173_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 2 2), upper := (rows 1 2 12 10 17 49 70), lower := (rows 1 2 12 10 17 49 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 32 127), good := (rows 78 78 78 78 94 126 78) }] }

theorem profile1_node173 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,17] 2 profile1_node173_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,17] 2 profile1_node173_cert).mp (by decide +kernel))

def profile1_node174_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 10 17 50 69), lower := (rows 1 2 12 10 17 50 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 48 64), good := (rows 14 14 14 14 62 62 78) }] }

theorem profile1_node174 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,18] 2 profile1_node174_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,18] 2 profile1_node174_cert).mp (by decide +kernel))

def profile1_node175_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 10 17 52 67), lower := (rows 1 2 12 10 17 52 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 48 64), good := (rows 14 14 14 14 62 62 78) },{ target := 1, region := (rows 127 0 12 8 127 44 64), good := (rows 17 17 61 61 17 53 81) }] }

theorem profile1_node175 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,20] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,20] 2 profile1_node175_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1,20] 2 profile1_node175_cert).mp (by decide +kernel))

def profile1_node169_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node169 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1] 2 (by decide) (choices 2) [3,5,6,17,18,20] profile1_node169_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,1] (choices 2) [3,5,6,17,18,20] profile1_node169_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node170
  · exact profile1_node171
  · exact profile1_node172
  · exact profile1_node173
  · exact profile1_node174
  · exact profile1_node175

def profile1_node177_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 12 10 18 37 81), lower := (rows 1 2 12 10 18 37 64), losses := [{ target := 1, region := (rows 127 0 12 8 16 44 80), good := (rows 1 1 45 45 81 37 65) }] }

theorem profile1_node177 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,2,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,2,5] 2 profile1_node177_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,2,5] 2 profile1_node177_cert).mp (by decide +kernel))

def profile1_node178_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 1 2 12 10 18 49 69), lower := (rows 1 2 12 10 18 49 64), losses := [{ target := 1, region := (rows 127 0 12 8 16 48 76), good := (rows 1 1 77 77 49 49 65) }] }

theorem profile1_node178 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,2,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,2,17] 2 profile1_node178_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,2,17] 2 profile1_node178_cert).mp (by decide +kernel))

def profile1_node176_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node176 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,2] 2 (by decide) (choices 2) [5,17] profile1_node176_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,2] (choices 2) [5,17] profile1_node176_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node177
  · exact profile1_node178

def profile1_node180_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 10 20 35 81), lower := (rows 1 2 12 10 20 35 64), losses := [] }

theorem profile1_node180 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,4,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,4,3] 2 profile1_node180_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,4,3] 2 profile1_node180_cert).mp (by decide +kernel))

def profile1_node181_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 10 20 49 67), lower := (rows 1 2 12 10 20 49 64), losses := [{ target := 1, region := (rows 127 0 12 8 28 60 64), good := (rows 1 1 61 61 53 49 65) }] }

theorem profile1_node181 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,4,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,4,17] 2 profile1_node181_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,4,17] 2 profile1_node181_cert).mp (by decide +kernel))

def profile1_node179_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node179 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,4] 2 (by decide) (choices 2) [3,17] profile1_node179_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2,4] (choices 2) [3,17] profile1_node179_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node180
  · exact profile1_node181

def profile1_node168_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node168 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2] 2 (by decide) (choices 1) [1,2,4] profile1_node168_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,2] (choices 1) [1,2,4] profile1_node168_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node169
  · exact profile1_node176
  · exact profile1_node179

def profile1_node184_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 12 17 35 82), lower := (rows 1 2 12 12 17 35 64), losses := [] }

theorem profile1_node184 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,1,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,1,3] 2 profile1_node184_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,1,3] 2 profile1_node184_cert).mp (by decide +kernel))

def profile1_node185_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 12 17 50 67), lower := (rows 1 2 12 12 17 50 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 48 64), good := (rows 14 14 14 14 62 62 78) }] }

theorem profile1_node185 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,1,18] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,1,18] 2 profile1_node185_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,1,18] 2 profile1_node185_cert).mp (by decide +kernel))

def profile1_node183_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node183 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,1] 2 (by decide) (choices 2) [3,18] profile1_node183_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,1] (choices 2) [3,18] profile1_node183_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node184
  · exact profile1_node185

def profile1_node187_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 12 18 35 81), lower := (rows 1 2 12 12 18 35 64), losses := [] }

theorem profile1_node187 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,2,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,2,3] 2 profile1_node187_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,2,3] 2 profile1_node187_cert).mp (by decide +kernel))

def profile1_node188_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 12 18 49 67), lower := (rows 1 2 12 12 18 49 64), losses := [{ target := 1, region := (rows 127 0 127 127 16 48 64), good := (rows 13 13 13 13 61 61 77) }] }

theorem profile1_node188 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,2,17] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,2,17] 2 profile1_node188_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,2,17] 2 profile1_node188_cert).mp (by decide +kernel))

def profile1_node186_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node186 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,2] 2 (by decide) (choices 2) [3,17] profile1_node186_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4,2] (choices 2) [3,17] profile1_node186_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node187
  · exact profile1_node188

def profile1_node182_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node182 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4] 2 (by decide) (choices 1) [1,2] profile1_node182_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,4] (choices 1) [1,2] profile1_node182_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node183
  · exact profile1_node186

def profile1_node191_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 24 17 35 70), lower := (rows 1 2 12 24 17 35 64), losses := [] }

theorem profile1_node191 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,1,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,1,3] 2 profile1_node191_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,1,3] 2 profile1_node191_cert).mp (by decide +kernel))

def profile1_node192_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 24 17 38 67), lower := (rows 1 2 12 24 17 38 64), losses := [{ target := 0, region := (rows 0 127 28 24 16 60 64), good := (rows 2 2 46 62 62 38 66) }] }

theorem profile1_node192 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,1,6] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,1,6] 2 profile1_node192_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,1,6] 2 profile1_node192_cert).mp (by decide +kernel))

def profile1_node190_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node190 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,1] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,1] 2 (by decide) (choices 2) [3,6] profile1_node190_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,1] (choices 2) [3,6] profile1_node190_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node191
  · exact profile1_node192

def profile1_node194_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 24 18 35 69), lower := (rows 1 2 12 24 18 35 64), losses := [] }

theorem profile1_node194 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,2,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,2,3] 2 profile1_node194_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,2,3] 2 profile1_node194_cert).mp (by decide +kernel))

def profile1_node195_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 24 18 37 67), lower := (rows 1 2 12 24 18 37 64), losses := [{ target := 1, region := (rows 127 0 28 24 16 60 64), good := (rows 1 1 45 61 61 37 65) }] }

theorem profile1_node195 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,2,5] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,2,5] 2 profile1_node195_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,2,5] 2 profile1_node195_cert).mp (by decide +kernel))

def profile1_node193_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node193 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,2] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,2] 2 (by decide) (choices 2) [3,5] profile1_node193_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,2] (choices 2) [3,5] profile1_node193_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node194
  · exact profile1_node195

def profile1_node197_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 3), upper := (rows 1 2 12 24 20 35 67), lower := (rows 1 2 12 24 20 35 64), losses := [] }

theorem profile1_node197 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,4,3] 2 :=
  bound_sound (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,4,3] 2 profile1_node197_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,4,3] 2 profile1_node197_cert).mp (by decide +kernel))

def profile1_node196_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node196 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,4] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,4] 2 (by decide) (choices 2) [3] profile1_node196_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16,4] (choices 2) [3] profile1_node196_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node197

def profile1_node189_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node189 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16] 2 (by decide) (choices 1) [1,2,4] profile1_node189_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8,16] (choices 1) [1,2,4] profile1_node189_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node190
  · exact profile1_node193
  · exact profile1_node196

def profile1_node153_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node153 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8] 2 (by decide) (choices 1) [1,2,4,16] profile1_node153_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0,8] (choices 1) [1,2,4,16] profile1_node153_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node154
  · exact profile1_node168
  · exact profile1_node182
  · exact profile1_node189

def profile1_node2_route : Route 7 := (fun mask => match mask with | 16 => (8,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile1_node2 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0] 2 (by decide) (choices 1) [1,2,8] profile1_node2_route
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0,0] (choices 1) [1,2,8] profile1_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node3
  · exact profile1_node78
  · exact profile1_node153

def profile1_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node1 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0] 2 (by decide) (choices 0) [0] profile1_node1_route
    (by change RowCover 7 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [0] (choices 0) [0] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node2

def profile1_node0_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node0 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [] 2 := by
  apply routed_branch (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [] 2 (by decide) (choices 0) [0] profile1_node0_route
    (by change RowCover 7 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [] (choices 0) [0] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node1

theorem profile1 : Upper (D (n:=7) [2,2,9,9,9,16,16]) (R (n:=7) [2,2,9,9,9,16,16]) [] 2 := profile1_node0

def profile2_node0_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 1), upper := (rows 63 63 63 63 63 63 127), lower := (rows 1 2 4 8 16 32 64), losses := [] }

theorem profile2_node0 : Upper (D (n:=7) [2,9,9,9,9,9,16]) (R (n:=7) [2,9,9,9,9,9,16]) [] 2 :=
  bound_sound (D (n:=7) [2,9,9,9,9,9,16]) (R (n:=7) [2,9,9,9,9,9,16]) [] 2 profile2_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [2,9,9,9,9,9,16]) (R (n:=7) [2,9,9,9,9,9,16]) [] 2 profile2_node0_cert).mp (by decide +kernel))

theorem profile2 : Upper (D (n:=7) [2,9,9,9,9,9,16]) (R (n:=7) [2,9,9,9,9,9,16]) [] 2 := profile2_node0

def profile3_node0_cert : Bound 7 := { allowed := (rows 0 0 0 0 0 0 0), upper := (rows 127 127 127 127 127 127 127), lower := (rows 1 2 4 8 16 32 64), losses := [] }

theorem profile3_node0 : Upper (D (n:=7) [9,9,9,9,9,9,9]) (R (n:=7) [9,9,9,9,9,9,9]) [] 2 :=
  bound_sound (D (n:=7) [9,9,9,9,9,9,9]) (R (n:=7) [9,9,9,9,9,9,9]) [] 2 profile3_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [9,9,9,9,9,9,9]) (R (n:=7) [9,9,9,9,9,9,9]) [] 2 profile3_node0_cert).mp (by decide +kernel))

theorem profile3 : Upper (D (n:=7) [9,9,9,9,9,9,9]) (R (n:=7) [9,9,9,9,9,9,9]) [] 2 := profile3_node0

def catalogue : List (List Nat) := [[2,2,2,9,16,16,16],[2,2,9,9,9,16,16],[2,9,9,9,9,9,16],[9,9,9,9,9,9,9]]

theorem catalogue_eq : profiles 7 7 0 7 7=catalogue := by decide +kernel

theorem profile_upper (xs : List Nat) (member : xs∈profiles 7 7 0 7 7) :
    Upper (n:=7) (D xs) (R xs) [] 2 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0
  · exact profile1
  · exact profile2
  · exact profile3
theorem upper (E : Graph (Fin 7)) (loops : Loopless E) (budget : arcCount E=7)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x) : score E≤2 := by
  have od (x) : SparseSupport.outdegree E x<7 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<7 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 7).map (SparseSupport.outdegree E)).sum=7 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 7).map (SparseSupport.indegree E)).sum=7 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    (by decide) od idg degree td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetSevenOrder7
