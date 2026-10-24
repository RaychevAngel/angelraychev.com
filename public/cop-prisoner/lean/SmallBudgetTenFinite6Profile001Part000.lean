import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile1_node2_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 23 23 39 43 16 32), lower := (rows 23 23 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 63 63), good := (rows 59 59 48 56 48 48) }] }

theorem profile1_node2 : Upper (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,21] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,21] 6 35 profile1_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,21] 6 35 profile1_node2_cert).mp (by decide +kernel))

def profile1_node3_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 23 39 55 59 16 32), lower := (rows 23 39 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 63 63), good := (rows 59 59 48 56 48 48) }] }

theorem profile1_node3 : Upper (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,37] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,37] 6 51 profile1_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,37] 6 51 profile1_node3_cert).mp (by decide +kernel))

def profile1_node4_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 23 51 39 47 16 32), lower := (rows 23 51 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 63 63), good := (rows 51 51 48 56 48 48) }] }

theorem profile1_node4 : Upper (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,49] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,49] 6 39 profile1_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,49] 6 39 profile1_node4_cert).mp (by decide +kernel))

def profile1_node5_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 23 54 39 43 16 32), lower := (rows 23 54 4 8 16 32), losses := [{ target := 0, region := (rows 0 7 4 8 63 63), good := (rows 54 54 54 56 48 48) }] }

theorem profile1_node5 : Upper (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,52] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,52] 6 35 profile1_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22,52] 6 35 profile1_node5_cert).mp (by decide +kernel))

def profile1_node1_column : Nat → Fin 6 := fun mask => match mask with | 13 => 3 | 25 => 3 | 41 => 3 | 28 => 3 | 44 => 3 | 56 => 3 | _ => 0

def profile1_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node1 : Upper (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [22] 6 (by decide) (choices 3) [21,37,49,52] profile1_node1_route profile1_node1_column
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node2
  · exact profile1_node3
  · exact profile1_node4
  · exact profile1_node5

def profile1_node6_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 51 55 55 63 16 32), lower := (rows 51 2 4 8 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 63 63), good := (rows 51 51 48 56 48 48) }] }

theorem profile1_node6 : Upper (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [50] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [50] 6 55 profile1_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [50] 6 55 profile1_node6_cert).mp (by decide +kernel))

def profile1_node7_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 53 55 55 63 16 32), lower := (rows 53 2 4 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 63 63), good := (rows 53 48 53 56 48 48) }] }

theorem profile1_node7 : Upper (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [52] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [52] 6 55 profile1_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [52] 6 55 profile1_node7_cert).mp (by decide +kernel))

def profile1_node0_column : Nat → Fin 6 := fun mask => match mask with | 14 => 3 | 26 => 3 | 42 => 3 | 28 => 3 | 44 => 3 | 56 => 3 | _ => 0

def profile1_node0_route : Route 6 := (fun mask => match mask with | 38 => (22,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node0 : Upper (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [] 6 (by decide) (choices 3) [22,50,52] profile1_node0_route profile1_node0_column
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node1
  · exact profile1_node6
  · exact profile1_node7

theorem profile1 : Upper (D (n:=6) [50,50,34,32,2,2]) (R (n:=6) [50,50,34,32,2,2]) [] 6 := profile1_node0


#print axioms profile1
end Delivery.SmallBudgetTenFinite6
