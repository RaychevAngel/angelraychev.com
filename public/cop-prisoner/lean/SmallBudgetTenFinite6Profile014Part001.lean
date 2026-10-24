import SmallBudgetTenFinite6Profile014Part000

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile14_node108_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node108_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node108 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile14_node108_route profile14_node108_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node109
  · exact profile14_node116
  · exact profile14_node117
  · exact profile14_node124
  · exact profile14_node125
  · exact profile14_node129

def profile14_node0_column : Nat → Fin 6 := fun mask => match mask with | 10 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node0_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node0 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [] 6 (by decide) (choices 2) [6,18,20,34,36,48] profile14_node0_route profile14_node0_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node1
  · exact profile14_node20
  · exact profile14_node51
  · exact profile14_node67
  · exact profile14_node95
  · exact profile14_node108

theorem profile14 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [] 6 := profile14_node0


#print axioms profile14
end Delivery.SmallBudgetTenFinite6
