import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0_node2_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 55 7 55 59 16 32), lower := (rows 55 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 63 63), good := (rows 59 59 48 56 48 48) }] }

theorem profile0_node2 : Upper (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,5] 6 51 profile0_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,5] 6 51 profile0_node2_cert).mp (by decide +kernel))

def profile0_node3_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 55 19 39 47 16 32), lower := (rows 55 19 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 63 63), good := (rows 51 51 48 56 48 48) }] }

theorem profile0_node3 : Upper (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,17] 6 39 profile0_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,17] 6 39 profile0_node3_cert).mp (by decide +kernel))

def profile0_node4_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 55 22 39 43 16 32), lower := (rows 55 22 4 8 16 32), losses := [{ target := 0, region := (rows 0 7 4 8 63 63), good := (rows 54 54 54 56 48 48) }] }

theorem profile0_node4 : Upper (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,20] 6 35 profile0_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,20] 6 35 profile0_node4_cert).mp (by decide +kernel))

def profile0_node5_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 55 50 7 15 16 32), lower := (rows 55 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 63 63), good := (rows 54 50 54 58 50 50) }] }

theorem profile0_node5 : Upper (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,48] 6 7 profile0_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54,48] 6 7 profile0_node5_cert).mp (by decide +kernel))

def profile0_node1_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile0_node1_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node1 : Upper (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [54] 6 (by decide) (choices 2) [5,17,20,48] profile0_node1_route profile0_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0_node2
  · exact profile0_node3
  · exact profile0_node4
  · exact profile0_node5

def profile0_node0_column : Nat → Fin 6 := fun mask => match mask with | 30 => 3 | 46 => 3 | 58 => 3 | 60 => 3 | _ => 0

def profile0_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node0 : Upper (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [] 6 (by decide) (choices 4) [54] profile0_node0_route profile0_node0_column
    (by change RowCover 6 4 (choices 4); exact cover ⟨4,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=6) [66,34,34,32,2,2]) (R (n:=6) [66,34,34,32,2,2]) [] 6 := profile0_node0


#print axioms profile0
end Delivery.SmallBudgetTenFinite6
