import SmallBudgetTenFinite7Profile033Part001

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile33_node258_cert : CutBound 7 := { lost := (rows 32 17 0 0 0 0 0), upper := (rows 81 98 55 63 55 55 64), lower := (rows 81 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 80 98 68 72 80 98 64) },{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 65 98 68 72 64 98 64) },{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 66 68 72 81 64 64) }] }

theorem profile33_node258 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,96] 6 55 profile33_node258_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,96] 6 55 profile33_node258_cert).mp (by decide +kernel))

def profile33_node160_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node160_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node160 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] profile33_node160_route profile33_node160_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node161
  · exact profile33_node178
  · exact profile33_node179
  · exact profile33_node195
  · exact profile33_node220
  · exact profile33_node240
  · exact profile33_node255
  · exact profile33_node256
  · exact profile33_node257
  · exact profile33_node258

def profile33_node0_column : Nat → Fin 7 := fun mask => match mask with | 10 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node0_route : Route 7 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 5 | 5 => 4 | _ => i)) | 68 => (66,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile33_node0 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [] 6 (by decide) (choices 2) [6,18,48,66,80] profile33_node0_route profile33_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile33_node1
  · exact profile33_node37
  · exact profile33_node102
  · exact profile33_node136
  · exact profile33_node160

theorem profile33 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [] 6 := profile33_node0


#print axioms profile33
end Delivery.SmallBudgetTenFinite7
