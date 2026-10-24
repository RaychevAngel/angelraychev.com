import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile16_node2_cert : CutBound 7 := { lost := (rows 0 0 32 32 32 0 0), upper := (rows 35 35 71 75 83 32 64), lower := (rows 35 35 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) }] }

theorem profile16_node2 : Upper (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [34,33] 6 67 profile16_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [34,33] 6 67 profile16_node2_cert).mp (by decide +kernel))

def profile16_node3_cert : CutBound 7 := { lost := (rows 64 32 0 0 0 0 0), upper := (rows 35 67 103 107 115 32 64), lower := (rows 35 67 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 67 67 68 72 80 64 64) },{ target := 6, region := (rows 3 2 4 8 16 127 0), good := (rows 35 35 36 40 48 32 32) }] }

theorem profile16_node3 : Upper (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [34,65] 6 99 profile16_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [34,65] 6 99 profile16_node3_cert).mp (by decide +kernel))

def profile16_node4_cert : CutBound 7 := { lost := (rows 0 1 32 32 32 0 0), upper := (rows 35 98 71 75 83 32 64), lower := (rows 35 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 66 68 72 80 64 64) }] }

theorem profile16_node4 : Upper (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [34,96] 6 67 profile16_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [34,96] 6 67 profile16_node4_cert).mp (by decide +kernel))

def profile16_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile16_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile16_node1 : Upper (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [34] 6 (by decide) (choices 2) [33,65,96] profile16_node1_route profile16_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node2
  · exact profile16_node3
  · exact profile16_node4

def profile16_node6_cert : CutBound 7 := { lost := (rows 2 0 32 32 32 0 0), upper := (rows 97 35 71 75 83 32 64), lower := (rows 97 35 4 8 16 32 64), losses := [{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 97 101 105 113 97 97) },{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 65 95 68 72 80 64 64) }] }

theorem profile16_node6 : Upper (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [96,33] 6 67 profile16_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [96,33] 6 67 profile16_node6_cert).mp (by decide +kernel))

def profile16_node7_cert : CutBound 7 := { lost := (rows 2 1 0 0 0 0 0), upper := (rows 97 98 7 11 19 32 64), lower := (rows 97 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 97 101 105 113 97 97) }] }

theorem profile16_node7 : Upper (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [96,96] 6 3 profile16_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [96,96] 6 3 profile16_node7_cert).mp (by decide +kernel))

def profile16_node5_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile16_node5_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile16_node5 : Upper (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [96] 6 (by decide) (choices 2) [33,96] profile16_node5_route profile16_node5_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile16_node6
  · exact profile16_node7

def profile16_node0_column : Nat → Fin 7 := fun mask => match mask with | 6 => 2 | 10 => 3 | 18 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile16_node0_route : Route 7 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile16_node0 : Upper (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [] 6 (by decide) (choices 2) [34,96] profile16_node0_route profile16_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile16_node1
  · exact profile16_node5

theorem profile16 : Upper (D (n:=7) [36,34,32,32,32,2,2]) (R (n:=7) [36,34,32,32,32,2,2]) [] 6 := profile16_node0


#print axioms profile16
end Delivery.SmallBudgetTenFinite7
