import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0_node2_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 115 19 103 107 16 32 64), lower := (rows 115 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 127 127), good := (rows 111 111 100 104 96 96 96) }] }

theorem profile0_node2 : Upper (D (n:=7) [66,34,32,32,2,2,2]) (R (n:=7) [66,34,32,32,2,2,2]) [114,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [66,34,32,32,2,2,2]) (R (n:=7) [66,34,32,32,2,2,2]) [114,17] 6 99 profile0_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [66,34,32,32,2,2,2]) (R (n:=7) [66,34,32,32,2,2,2]) [114,17] 6 99 profile0_node2_cert).mp (by decide +kernel))

def profile0_node3_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 115 50 71 75 16 32 64), lower := (rows 115 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 118 122 114 114 114) },{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile0_node3 : Upper (D (n:=7) [66,34,32,32,2,2,2]) (R (n:=7) [66,34,32,32,2,2,2]) [114,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [66,34,32,32,2,2,2]) (R (n:=7) [66,34,32,32,2,2,2]) [114,48] 6 67 profile0_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [66,34,32,32,2,2,2]) (R (n:=7) [66,34,32,32,2,2,2]) [114,48] 6 67 profile0_node3_cert).mp (by decide +kernel))

def profile0_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile0_node1_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node1 : Upper (D (n:=7) [66,34,32,32,2,2,2]) (R (n:=7) [66,34,32,32,2,2,2]) [114] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [66,34,32,32,2,2,2]) (R (n:=7) [66,34,32,32,2,2,2]) [114] 6 (by decide) (choices 2) [17,48] profile0_node1_route profile0_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node2
  · exact profile0_node3

def profile0_node0_column : Nat → Fin 7 := fun mask => match mask with | 30 => 2 | 46 => 2 | 78 => 2 | 54 => 2 | 86 => 2 | 102 => 2 | 58 => 3 | 90 => 3 | 106 => 3 | 60 => 2 | 92 => 2 | 108 => 2 | 116 => 2 | 120 => 3 | _ => 0

def profile0_node0_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node0 : Upper (D (n:=7) [66,34,32,32,2,2,2]) (R (n:=7) [66,34,32,32,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [66,34,32,32,2,2,2]) (R (n:=7) [66,34,32,32,2,2,2]) [] 6 (by decide) (choices 4) [114] profile0_node0_route profile0_node0_column
    (by change RowCover 7 4 (choices 4); exact cover ⟨4,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=7) [66,34,32,32,2,2,2]) (R (n:=7) [66,34,32,32,2,2,2]) [] 6 := profile0_node0


#print axioms profile0
end Delivery.SmallBudgetTenFinite7
