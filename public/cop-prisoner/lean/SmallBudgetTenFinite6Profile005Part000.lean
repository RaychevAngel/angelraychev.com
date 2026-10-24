import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile5_node2_cert : CutBound 6 := { lost := (rows 0 0 0 4 4 0), upper := (rows 7 7 39 43 51 32), lower := (rows 7 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 19 63), good := (rows 59 59 32 40 48 32) }] }

theorem profile5_node2 : Upper (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [6,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [6,5] 6 35 profile5_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [6,5] 6 35 profile5_node2_cert).mp (by decide +kernel))

def profile5_node3_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 7 35 39 47 55 32), lower := (rows 7 35 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 35 35 32 40 48 32) }] }

theorem profile5_node3 : Upper (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [6,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [6,33] 6 39 profile5_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [6,33] 6 39 profile5_node3_cert).mp (by decide +kernel))

def profile5_node4_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 7 38 39 43 51 32), lower := (rows 7 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 7 4 8 16 63), good := (rows 38 38 38 40 48 32) }] }

theorem profile5_node4 : Upper (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [6,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [6,36] 6 35 profile5_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [6,36] 6 35 profile5_node4_cert).mp (by decide +kernel))

def profile5_node1_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile5_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile5_node1 : Upper (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [6] 6 (by decide) (choices 2) [5,33,36] profile5_node1_route profile5_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node2
  · exact profile5_node3
  · exact profile5_node4

def profile5_node5_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 35 39 39 47 55 32), lower := (rows 35 2 4 8 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 35 32 40 48 32) }] }

theorem profile5_node5 : Upper (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [34] 6 39 profile5_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [34] 6 39 profile5_node5_cert).mp (by decide +kernel))

def profile5_node0_column : Nat → Fin 6 := fun mask => match mask with | 10 => 3 | 18 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile5_node0_route : Route 6 := (fun mask => match mask with | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile5_node0 : Upper (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [] 6 (by decide) (choices 2) [6,34] profile5_node0_route profile5_node0_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node1
  · exact profile5_node5

theorem profile5 : Upper (D (n:=6) [36,34,34,32,32,2]) (R (n:=6) [36,34,34,32,32,2]) [] 6 := profile5_node0


#print axioms profile5
end Delivery.SmallBudgetTenFinite6
