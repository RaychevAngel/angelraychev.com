import SmallRowPrefixCut
import SmallBudgetProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
6 vertices with 9 arrows and the stated degree restriction. -/
namespace Delivery.SmallBudgetNineFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
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

def profile0_node3_cert : CutBound 6 := { lost := (rows 16 16 0 0 0 0), upper := (rows 7 11 28 56 48 48), lower := (rows 7 11 28 8 16 32), losses := [{ target := 4, region := (rows 5 6 4 8 0 32), good := (rows 7 11 15 8 0 32) }] }

theorem profile0_node3 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9,24] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9,24] 5 profile0_node3_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9,24] 5 profile0_node3_cert).mp (by decide +kernel))

def profile0_node5_cert : CutBound 6 := { lost := (rows 32 32 0 0 0 0), upper := (rows 7 11 52 24 56 40), lower := (rows 7 11 52 24 16 32), losses := [{ target := 5, region := (rows 5 7 4 28 16 0), good := (rows 15 11 31 24 24 0) }] }

theorem profile0_node5 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9,48,16] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9,48,16] 5 profile0_node5_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9,48,16] 5 profile0_node5_cert).mp (by decide +kernel))

def profile0_node4_route : Route 6 := (fun mask => match mask with | 32 => (16,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node4 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9,48] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9,48] 5 (by decide) (choices 1) [16] profile0_node4_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9,48] (choices 1) [16] profile0_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node5

def profile0_node2_route : Route 6 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node2 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9] 5 (by decide) (choices 2) [24,48] profile0_node2_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,9] (choices 2) [24,48] profile0_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node3
  · exact profile0_node4

def profile0_node7_cert : CutBound 6 := { lost := (rows 16 0 16 0 0 0), upper := (rows 7 26 13 56 48 48), lower := (rows 7 26 13 8 16 32), losses := [{ target := 4, region := (rows 3 2 6 8 0 32), good := (rows 7 15 13 8 0 32) }] }

theorem profile0_node7 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,9] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,9] 5 profile0_node7_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,9] 5 profile0_node7_cert).mp (by decide +kernel))

def profile0_node8_cert : Bound 6 := { allowed := (rows 56 32 32 0 0 0), upper := (rows 7 26 28 41 49 33), lower := (rows 7 26 28 8 16 32), losses := [] }

theorem profile0_node8 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,24] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,24] 5 profile0_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,24] 5 profile0_node8_cert).mp (by decide +kernel))

def profile0_node10_cert : CutBound 6 := { lost := (rows 16 0 16 0 0 0), upper := (rows 7 26 37 24 56 40), lower := (rows 7 26 37 24 16 32), losses := [{ target := 4, region := (rows 3 2 7 8 0 42), good := (rows 39 47 37 40 0 32) }] }

theorem profile0_node10 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,33,16] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,33,16] 5 profile0_node10_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,33,16] 5 profile0_node10_cert).mp (by decide +kernel))

def profile0_node11_cert : Bound 6 := { allowed := (rows 56 0 24 0 0 0), upper := (rows 7 26 37 40 24 56), lower := (rows 7 26 37 40 16 32), losses := [{ target := 5, region := (rows 1 10 4 8 26 0), good := (rows 23 26 5 26 16 0) }] }

theorem profile0_node11 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,33,32] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,33,32] 5 profile0_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,33,32] 5 profile0_node11_cert).mp (by decide +kernel))

def profile0_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node9 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,33] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,33] 5 (by decide) (choices 1) [16,32] profile0_node9_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,33] (choices 1) [16,32] profile0_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node10
  · exact profile0_node11

def profile0_node12_cert : Bound 6 := { allowed := (rows 56 32 16 0 0 0), upper := (rows 7 26 44 57 49 49), lower := (rows 7 26 44 8 16 32), losses := [] }

theorem profile0_node12 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,40] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,40] 5 profile0_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24,40] 5 profile0_node12_cert).mp (by decide +kernel))

def profile0_node6_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile0_node6 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24] 5 (by decide) (choices 2) [9,24,33,40] profile0_node6_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6,24] (choices 2) [9,24,33,40] profile0_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0_node7
  · exact profile0_node8
  · exact profile0_node9
  · exact profile0_node12

def profile0_node1_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 33 => (9,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile0_node1 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6] 5 (by decide) (choices 2) [9,24] profile0_node1_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [6] (choices 2) [9,24] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node2
  · exact profile0_node6

def profile0_node15_cert : CutBound 6 := { lost := (rows 16 16 0 0 0 0), upper := (rows 11 7 28 56 48 48), lower := (rows 11 7 28 8 16 32), losses := [{ target := 4, region := (rows 5 6 4 8 0 32), good := (rows 11 7 15 8 0 32) }] }

theorem profile0_node15 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5,24] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5,24] 5 profile0_node15_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5,24] 5 profile0_node15_cert).mp (by decide +kernel))

def profile0_node17_cert : CutBound 6 := { lost := (rows 32 32 0 0 0 0), upper := (rows 11 7 52 24 56 40), lower := (rows 11 7 52 24 16 32), losses := [{ target := 5, region := (rows 7 6 4 28 16 0), good := (rows 11 15 31 24 24 0) }] }

theorem profile0_node17 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5,48,16] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5,48,16] 5 profile0_node17_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5,48,16] 5 profile0_node17_cert).mp (by decide +kernel))

def profile0_node16_route : Route 6 := (fun mask => match mask with | 32 => (16,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node16 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5,48] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5,48] 5 (by decide) (choices 1) [16] profile0_node16_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5,48] (choices 1) [16] profile0_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node17

def profile0_node14_route : Route 6 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node14 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5] 5 (by decide) (choices 2) [24,48] profile0_node14_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,5] (choices 2) [24,48] profile0_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node15
  · exact profile0_node16

def profile0_node18_cert : CutBound 6 := { lost := (rows 16 16 8 0 0 0), upper := (rows 11 11 52 60 52 52), lower := (rows 11 11 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 63 0 63 63), good := (rows 55 55 52 52 52 52) },{ target := 4, region := (rows 11 11 4 8 0 32), good := (rows 11 11 4 11 0 32) }] }

theorem profile0_node18 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,9] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,9] 5 profile0_node18_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,9] 5 profile0_node18_cert).mp (by decide +kernel))

def profile0_node19_cert : CutBound 6 := { lost := (rows 16 0 8 0 0 0), upper := (rows 11 14 53 57 49 49), lower := (rows 11 14 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 5 0 17 33), good := (rows 55 6 4 0 16 32) },{ target := 4, region := (rows 3 2 4 8 0 32), good := (rows 11 15 4 8 0 32) }] }

theorem profile0_node19 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,12] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,12] 5 profile0_node19_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,12] 5 profile0_node19_cert).mp (by decide +kernel))

def profile0_node21_cert : Bound 6 := { allowed := (rows 48 40 32 0 0 0), upper := (rows 11 19 28 44 52 36), lower := (rows 11 19 28 8 16 32), losses := [] }

theorem profile0_node21 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17,24] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17,24] 5 profile0_node21_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17,24] 5 profile0_node21_cert).mp (by decide +kernel))

def profile0_node22_cert : Bound 6 := { allowed := (rows 48 40 16 0 0 0), upper := (rows 11 19 44 60 52 52), lower := (rows 11 19 44 8 16 32), losses := [] }

theorem profile0_node22 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17,40] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17,40] 5 profile0_node22_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17,40] 5 profile0_node22_cert).mp (by decide +kernel))

def profile0_node23_cert : Bound 6 := { allowed := (rows 48 40 8 0 0 0), upper := (rows 11 19 52 44 60 44), lower := (rows 11 19 52 8 16 32), losses := [] }

theorem profile0_node23 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17,48] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17,48] 5 profile0_node23_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17,48] 5 profile0_node23_cert).mp (by decide +kernel))

def profile0_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node20 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17] 5 (by decide) (choices 2) [24,40,48] profile0_node20_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,17] (choices 2) [24,40,48] profile0_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node21
  · exact profile0_node22
  · exact profile0_node23

def profile0_node25_cert : Bound 6 := { allowed := (rows 48 32 48 0 0 0), upper := (rows 11 22 13 56 48 48), lower := (rows 11 22 13 8 16 32), losses := [{ target := 3, region := (rows 1 6 4 0 63 63), good := (rows 51 54 55 48 48 48) }] }

theorem profile0_node25 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,9] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,9] 5 profile0_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,9] 5 profile0_node25_cert).mp (by decide +kernel))

def profile0_node26_cert : Bound 6 := { allowed := (rows 48 32 40 0 0 0), upper := (rows 11 22 21 40 56 40), lower := (rows 11 22 21 8 16 32), losses := [{ target := 3, region := (rows 1 6 4 0 16 32), good := (rows 3 22 23 0 16 32) }] }

theorem profile0_node26 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,17] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,17] 5 profile0_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,17] 5 profile0_node26_cert).mp (by decide +kernel))

def profile0_node27_cert : Bound 6 := { allowed := (rows 48 40 32 0 0 0), upper := (rows 11 22 28 41 49 33), lower := (rows 11 22 28 8 16 32), losses := [] }

theorem profile0_node27 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,24] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,24] 5 profile0_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,24] 5 profile0_node27_cert).mp (by decide +kernel))

def profile0_node29_cert : Bound 6 := { allowed := (rows 48 40 8 0 0 0), upper := (rows 11 22 37 24 56 40), lower := (rows 11 22 37 24 16 32), losses := [{ target := 4, region := (rows 1 2 5 8 0 41), good := (rows 47 6 37 40 0 32) }] }

theorem profile0_node29 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,33,16] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,33,16] 5 profile0_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,33,16] 5 profile0_node29_cert).mp (by decide +kernel))

def profile0_node30_cert : Bound 6 := { allowed := (rows 32 40 24 0 0 0), upper := (rows 11 22 37 40 24 56), lower := (rows 11 22 37 40 16 32), losses := [{ target := 4, region := (rows 3 2 4 44 0 32), good := (rows 11 15 45 40 0 40) }] }

theorem profile0_node30 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,33,32] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,33,32] 5 profile0_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,33,32] 5 profile0_node30_cert).mp (by decide +kernel))

def profile0_node28_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node28 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,33] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,33] 5 (by decide) (choices 1) [16,32] profile0_node28_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,33] (choices 1) [16,32] profile0_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node29
  · exact profile0_node30

def profile0_node31_cert : Bound 6 := { allowed := (rows 48 40 16 0 0 0), upper := (rows 11 22 44 57 49 49), lower := (rows 11 22 44 8 16 32), losses := [] }

theorem profile0_node31 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,40] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,40] 5 profile0_node31_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,40] 5 profile0_node31_cert).mp (by decide +kernel))

def profile0_node32_cert : Bound 6 := { allowed := (rows 48 40 8 0 0 0), upper := (rows 11 22 52 41 57 41), lower := (rows 11 22 52 8 16 32), losses := [] }

theorem profile0_node32 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,48] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,48] 5 profile0_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20,48] 5 profile0_node32_cert).mp (by decide +kernel))

def profile0_node24_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node24 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20] 5 (by decide) (choices 2) [9,17,24,33,40,48] profile0_node24_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,20] (choices 2) [9,17,24,33,40,48] profile0_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node25
  · exact profile0_node26
  · exact profile0_node27
  · exact profile0_node28
  · exact profile0_node31
  · exact profile0_node32

def profile0_node33_cert : Bound 6 := { allowed := (rows 48 32 48 0 0 0), upper := (rows 11 26 53 61 53 53), lower := (rows 11 26 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 5 0 17 33), good := (rows 55 18 4 0 16 32) }] }

theorem profile0_node33 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,24] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,24] 5 profile0_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,24] 5 profile0_node33_cert).mp (by decide +kernel))

def profile0_node35_cert : Bound 6 := { allowed := (rows 48 8 48 0 0 0), upper := (rows 11 50 13 60 52 52), lower := (rows 11 50 13 8 16 32), losses := [] }

theorem profile0_node35 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,9] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,9] 5 profile0_node35_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,9] 5 profile0_node35_cert).mp (by decide +kernel))

def profile0_node36_cert : Bound 6 := { allowed := (rows 48 8 40 0 0 0), upper := (rows 11 50 21 44 60 44), lower := (rows 11 50 21 8 16 32), losses := [] }

theorem profile0_node36 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,17] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,17] 5 profile0_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,17] 5 profile0_node36_cert).mp (by decide +kernel))

def profile0_node37_cert : Bound 6 := { allowed := (rows 48 8 32 0 0 0), upper := (rows 11 50 28 45 53 37), lower := (rows 11 50 28 8 16 32), losses := [] }

theorem profile0_node37 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,24] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,24] 5 profile0_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,24] 5 profile0_node37_cert).mp (by decide +kernel))

def profile0_node38_cert : Bound 6 := { allowed := (rows 48 8 8 0 0 0), upper := (rows 11 50 52 13 29 45), lower := (rows 11 50 52 8 16 32), losses := [] }

theorem profile0_node38 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,48] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,48] 5 profile0_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48,48] 5 profile0_node38_cert).mp (by decide +kernel))

def profile0_node34_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node34 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48] 5 (by decide) (choices 2) [9,17,24,48] profile0_node34_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10,48] (choices 2) [9,17,24,48] profile0_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0_node35
  · exact profile0_node36
  · exact profile0_node37
  · exact profile0_node38

def profile0_node13_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node13 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10] 5 (by decide) (choices 2) [5,9,12,17,20,24,48] profile0_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [10] (choices 2) [5,9,12,17,20,24,48] profile0_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node14
  · exact profile0_node18
  · exact profile0_node19
  · exact profile0_node20
  · exact profile0_node24
  · exact profile0_node33
  · exact profile0_node34

def profile0_node41_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 25 7 14 56 48 48), lower := (rows 25 7 14 8 16 32), losses := [{ target := 4, region := (rows 1 3 5 8 0 32), good := (rows 15 7 14 8 0 32) }] }

theorem profile0_node41 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,10] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,10] 5 profile0_node41_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,10] 5 profile0_node41_cert).mp (by decide +kernel))

def profile0_node42_cert : Bound 6 := { allowed := (rows 32 56 32 0 0 0), upper := (rows 25 7 28 42 50 34), lower := (rows 25 7 28 8 16 32), losses := [] }

theorem profile0_node42 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,24] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,24] 5 profile0_node42_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,24] 5 profile0_node42_cert).mp (by decide +kernel))

def profile0_node44_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 25 7 38 24 56 40), lower := (rows 25 7 38 24 16 32), losses := [{ target := 4, region := (rows 1 3 7 8 0 41), good := (rows 47 39 38 40 0 32) }] }

theorem profile0_node44 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,34,16] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,34,16] 5 profile0_node44_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,34,16] 5 profile0_node44_cert).mp (by decide +kernel))

def profile0_node45_cert : Bound 6 := { allowed := (rows 0 56 24 0 0 0), upper := (rows 25 7 38 40 24 56), lower := (rows 25 7 38 40 16 32), losses := [{ target := 5, region := (rows 9 2 4 8 25 0), good := (rows 25 23 6 25 16 0) }] }

theorem profile0_node45 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,34,32] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,34,32] 5 profile0_node45_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,34,32] 5 profile0_node45_cert).mp (by decide +kernel))

def profile0_node43_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node43 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,34] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,34] 5 (by decide) (choices 1) [16,32] profile0_node43_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,34] (choices 1) [16,32] profile0_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node44
  · exact profile0_node45

def profile0_node46_cert : Bound 6 := { allowed := (rows 32 56 16 0 0 0), upper := (rows 25 7 44 58 50 50), lower := (rows 25 7 44 8 16 32), losses := [] }

theorem profile0_node46 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,40] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,40] 5 profile0_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5,40] 5 profile0_node46_cert).mp (by decide +kernel))

def profile0_node40_route : Route 6 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile0_node40 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5] 5 (by decide) (choices 2) [10,24,34,40] profile0_node40_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,5] (choices 2) [10,24,34,40] profile0_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0_node41
  · exact profile0_node42
  · exact profile0_node43
  · exact profile0_node46

def profile0_node47_cert : Bound 6 := { allowed := (rows 32 48 48 0 0 0), upper := (rows 25 11 54 62 54 54), lower := (rows 25 11 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 6 0 18 34), good := (rows 17 55 4 0 16 32) }] }

theorem profile0_node47 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,9] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,9] 5 profile0_node47_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,9] 5 profile0_node47_cert).mp (by decide +kernel))

def profile0_node49_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 25 14 7 56 48 48), lower := (rows 25 14 7 8 16 32), losses := [{ target := 4, region := (rows 1 3 5 8 0 32), good := (rows 15 14 7 8 0 32) }] }

theorem profile0_node49 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,3] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,3] 5 profile0_node49_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,3] 5 profile0_node49_cert).mp (by decide +kernel))

def profile0_node50_cert : Bound 6 := { allowed := (rows 32 48 40 0 0 0), upper := (rows 25 14 21 42 50 34), lower := (rows 25 14 21 8 16 32), losses := [] }

theorem profile0_node50 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,17] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,17] 5 profile0_node50_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,17] 5 profile0_node50_cert).mp (by decide +kernel))

def profile0_node51_cert : Bound 6 := { allowed := (rows 32 48 40 0 0 0), upper := (rows 25 14 22 41 49 33), lower := (rows 25 14 22 8 16 32), losses := [] }

theorem profile0_node51 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,18] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,18] 5 profile0_node51_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,18] 5 profile0_node51_cert).mp (by decide +kernel))

def profile0_node52_cert : Bound 6 := { allowed := (rows 32 48 24 0 0 0), upper := (rows 25 14 37 58 50 50), lower := (rows 25 14 37 8 16 32), losses := [] }

theorem profile0_node52 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,33] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,33] 5 profile0_node52_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,33] 5 profile0_node52_cert).mp (by decide +kernel))

def profile0_node53_cert : Bound 6 := { allowed := (rows 32 48 24 0 0 0), upper := (rows 25 14 38 57 49 49), lower := (rows 25 14 38 8 16 32), losses := [] }

theorem profile0_node53 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,34] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,34] 5 profile0_node53_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,34] 5 profile0_node53_cert).mp (by decide +kernel))

def profile0_node54_cert : Bound 6 := { allowed := (rows 32 48 8 0 0 0), upper := (rows 25 14 52 43 51 35), lower := (rows 25 14 52 8 16 32), losses := [] }

theorem profile0_node54 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,48] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,48] 5 profile0_node54_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12,48] 5 profile0_node54_cert).mp (by decide +kernel))

def profile0_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node48 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12] 5 (by decide) (choices 2) [3,17,18,33,34,48] profile0_node48_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,12] (choices 2) [3,17,18,33,34,48] profile0_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node49
  · exact profile0_node50
  · exact profile0_node51
  · exact profile0_node52
  · exact profile0_node53
  · exact profile0_node54

def profile0_node55_cert : Bound 6 := { allowed := (rows 32 32 56 0 0 0), upper := (rows 25 26 39 47 55 39), lower := (rows 25 26 4 8 16 32), losses := [] }

theorem profile0_node55 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,24] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,24] 5 profile0_node55_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,24] 5 profile0_node55_cert).mp (by decide +kernel))

def profile0_node57_cert : Bound 6 := { allowed := (rows 32 24 48 0 0 0), upper := (rows 25 35 14 60 52 52), lower := (rows 25 35 14 8 16 32), losses := [] }

theorem profile0_node57 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,10] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,10] 5 profile0_node57_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,10] 5 profile0_node57_cert).mp (by decide +kernel))

def profile0_node58_cert : Bound 6 := { allowed := (rows 32 24 32 0 0 0), upper := (rows 25 35 28 46 54 38), lower := (rows 25 35 28 8 16 32), losses := [] }

theorem profile0_node58 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,24] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,24] 5 profile0_node58_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,24] 5 profile0_node58_cert).mp (by decide +kernel))

def profile0_node59_cert : Bound 6 := { allowed := (rows 32 24 24 0 0 0), upper := (rows 25 35 38 28 28 60), lower := (rows 25 35 38 8 16 32), losses := [] }

theorem profile0_node59 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,34] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,34] 5 profile0_node59_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,34] 5 profile0_node59_cert).mp (by decide +kernel))

def profile0_node60_cert : Bound 6 := { allowed := (rows 32 24 16 0 0 0), upper := (rows 25 35 44 30 22 54), lower := (rows 25 35 44 8 16 32), losses := [] }

theorem profile0_node60 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,40] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,40] 5 profile0_node60_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33,40] 5 profile0_node60_cert).mp (by decide +kernel))

def profile0_node56_route : Route 6 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile0_node56 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33] 5 (by decide) (choices 2) [10,24,34,40] profile0_node56_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,33] (choices 2) [10,24,34,40] profile0_node56_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0_node57
  · exact profile0_node58
  · exact profile0_node59
  · exact profile0_node60

def profile0_node63_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 25 38 7 24 56 40), lower := (rows 25 38 7 24 16 32), losses := [{ target := 4, region := (rows 1 7 5 8 0 41), good := (rows 47 38 39 40 0 32) }] }

theorem profile0_node63 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,3,16] 5 :=
  cut_bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,3,16] 5 profile0_node63_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,3,16] 5 profile0_node63_cert).mp (by decide +kernel))

def profile0_node64_cert : Bound 6 := { allowed := (rows 0 24 56 0 0 0), upper := (rows 25 38 7 40 24 56), lower := (rows 25 38 7 40 16 32), losses := [{ target := 5, region := (rows 9 2 4 8 25 0), good := (rows 25 6 23 25 16 0) }] }

theorem profile0_node64 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,3,32] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,3,32] 5 profile0_node64_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,3,32] 5 profile0_node64_cert).mp (by decide +kernel))

def profile0_node62_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node62 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,3] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,3] 5 (by decide) (choices 1) [16,32] profile0_node62_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,3] (choices 1) [16,32] profile0_node62_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node63
  · exact profile0_node64

def profile0_node65_cert : Bound 6 := { allowed := (rows 32 24 48 0 0 0), upper := (rows 25 38 13 58 50 50), lower := (rows 25 38 13 8 16 32), losses := [] }

theorem profile0_node65 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,9] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,9] 5 profile0_node65_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,9] 5 profile0_node65_cert).mp (by decide +kernel))

def profile0_node66_cert : Bound 6 := { allowed := (rows 32 24 48 0 0 0), upper := (rows 25 38 14 57 49 49), lower := (rows 25 38 14 8 16 32), losses := [] }

theorem profile0_node66 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,10] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,10] 5 profile0_node66_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,10] 5 profile0_node66_cert).mp (by decide +kernel))

def profile0_node67_cert : Bound 6 := { allowed := (rows 32 24 32 0 0 0), upper := (rows 25 38 28 43 51 35), lower := (rows 25 38 28 8 16 32), losses := [] }

theorem profile0_node67 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,24] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,24] 5 profile0_node67_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,24] 5 profile0_node67_cert).mp (by decide +kernel))

def profile0_node68_cert : Bound 6 := { allowed := (rows 32 24 24 0 0 0), upper := (rows 25 38 37 26 26 58), lower := (rows 25 38 37 8 16 32), losses := [] }

theorem profile0_node68 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,33] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,33] 5 profile0_node68_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,33] 5 profile0_node68_cert).mp (by decide +kernel))

def profile0_node69_cert : Bound 6 := { allowed := (rows 32 24 24 0 0 0), upper := (rows 25 38 38 25 25 57), lower := (rows 25 38 38 8 16 32), losses := [] }

theorem profile0_node69 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,34] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,34] 5 profile0_node69_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,34] 5 profile0_node69_cert).mp (by decide +kernel))

def profile0_node70_cert : Bound 6 := { allowed := (rows 32 24 16 0 0 0), upper := (rows 25 38 44 27 19 51), lower := (rows 25 38 44 8 16 32), losses := [] }

theorem profile0_node70 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,40] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,40] 5 profile0_node70_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36,40] 5 profile0_node70_cert).mp (by decide +kernel))

def profile0_node61_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile0_node61 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36] 5 (by decide) (choices 2) [3,9,10,24,33,34,40] profile0_node61_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,36] (choices 2) [3,9,10,24,33,34,40] profile0_node61_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node62
  · exact profile0_node65
  · exact profile0_node66
  · exact profile0_node67
  · exact profile0_node68
  · exact profile0_node69
  · exact profile0_node70

def profile0_node71_cert : Bound 6 := { allowed := (rows 32 16 56 0 0 0), upper := (rows 25 42 55 63 55 55), lower := (rows 25 42 4 8 16 32), losses := [] }

theorem profile0_node71 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,40] 5 :=
  bound_sound (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,40] 5 profile0_node71_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24,40] 5 profile0_node71_cert).mp (by decide +kernel))

def profile0_node39_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile0_node39 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24] 5 (by decide) (choices 2) [5,9,12,24,33,36,40] profile0_node39_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [24] (choices 2) [5,9,12,24,33,36,40] profile0_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node40
  · exact profile0_node47
  · exact profile0_node48
  · exact profile0_node55
  · exact profile0_node56
  · exact profile0_node61
  · exact profile0_node71

def profile0_node0_route : Route 6 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 34 => (10,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 12 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 20 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | _ => i)) | 36 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | 3 => 5 | 5 => 3 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile0_node0 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [] 5 := by
  apply routed_branch (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [] 5 (by decide) (choices 2) [6,10,24] profile0_node0_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [] (choices 2) [6,10,24] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node1
  · exact profile0_node13
  · exact profile0_node39

theorem profile0 : Upper (D (n:=6) [33,33,33,18,18,18]) (R (n:=6) [33,33,33,18,18,18]) [] 5 := profile0_node0

def catalogue : List (List Nat) := [[18,18,18,33,33,33]]

theorem catalogue_eq : hardProfiles 6 9 5 false=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 6 9 5 false) :
    Upper (n:=6) (D xs.reverse) (R xs.reverse) [] 5 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0
theorem profile_upper (xs : List Nat) (member : xs∈profiles 6 false 6 0 9 9) :
    Upper (n:=6) (D xs.reverse) (R xs.reverse) [] 5 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 6)) (loops : Loopless E) (budget : arcCount E=9)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (false=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤5 := by
  have od (x) : SparseSupport.outdegree E x<6 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<6 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 6).map (SparseSupport.outdegree E)).sum=9 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 6).map (SparseSupport.indegree E)).sum=9 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    false (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetNineFinite6
