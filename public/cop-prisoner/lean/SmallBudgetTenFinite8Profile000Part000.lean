import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0_node2_cert : CutBound 8 := { lost := (rows 0 32 16 16 0 0 0 0), upper := (rows 241 19 229 233 16 32 64 128), lower := (rows 241 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 7 11 0 255 255 255), good := (rows 237 239 228 232 224 224 224 224) },{ target := 5, region := (rows 1 3 4 8 255 0 255 255), good := (rows 211 211 212 216 208 208 208 208) }] }

theorem profile0_node2 : Upper (D (n:=8) [66,32,32,32,2,2,2,2]) (R (n:=8) [66,32,32,32,2,2,2,2]) [240,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [66,32,32,32,2,2,2,2]) (R (n:=8) [66,32,32,32,2,2,2,2]) [240,17] 6 225 profile0_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [66,32,32,32,2,2,2,2]) (R (n:=8) [66,32,32,32,2,2,2,2]) [240,17] 6 225 profile0_node2_cert).mp (by decide +kernel))

def profile0_node3_cert : CutBound 8 := { lost := (rows 0 1 16 16 0 0 0 0), upper := (rows 241 50 197 201 16 32 64 128), lower := (rows 241 50 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 4, region := (rows 1 2 5 9 0 255 255 255), good := (rows 237 226 228 232 224 224 224 224) }] }

theorem profile0_node3 : Upper (D (n:=8) [66,32,32,32,2,2,2,2]) (R (n:=8) [66,32,32,32,2,2,2,2]) [240,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [66,32,32,32,2,2,2,2]) (R (n:=8) [66,32,32,32,2,2,2,2]) [240,48] 6 193 profile0_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [66,32,32,32,2,2,2,2]) (R (n:=8) [66,32,32,32,2,2,2,2]) [240,48] 6 193 profile0_node3_cert).mp (by decide +kernel))

def profile0_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile0_node1_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile0_node1 : Upper (D (n:=8) [66,32,32,32,2,2,2,2]) (R (n:=8) [66,32,32,32,2,2,2,2]) [240] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [66,32,32,32,2,2,2,2]) (R (n:=8) [66,32,32,32,2,2,2,2]) [240] 6 (by decide) (choices 2) [17,48] profile0_node1_route profile0_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node2
  · exact profile0_node3

def profile0_node0_column : Nat → Fin 8 := fun mask => match mask with | 30 => 1 | 46 => 1 | 78 => 1 | 142 => 1 | 54 => 1 | 86 => 1 | 150 => 1 | 102 => 1 | 166 => 1 | 198 => 1 | 58 => 1 | 90 => 1 | 154 => 1 | 106 => 1 | 170 => 1 | 202 => 1 | 114 => 1 | 178 => 1 | 210 => 1 | 226 => 1 | 60 => 2 | 92 => 2 | 156 => 2 | 108 => 2 | 172 => 2 | 204 => 2 | 116 => 2 | 180 => 2 | 212 => 2 | 228 => 2 | 120 => 3 | 184 => 3 | 216 => 3 | 232 => 3 | _ => 0

def profile0_node0_route : Route 8 := (fun mask => (mask,id))

theorem profile0_node0 : Upper (D (n:=8) [66,32,32,32,2,2,2,2]) (R (n:=8) [66,32,32,32,2,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [66,32,32,32,2,2,2,2]) (R (n:=8) [66,32,32,32,2,2,2,2]) [] 6 (by decide) (choices 4) [240] profile0_node0_route profile0_node0_column
    (by change RowCover 8 4 (choices 4); exact cover ⟨4,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=8) [66,32,32,32,2,2,2,2]) (R (n:=8) [66,32,32,32,2,2,2,2]) [] 6 := profile0_node0


#print axioms profile0
end Delivery.SmallBudgetTenFinite8
