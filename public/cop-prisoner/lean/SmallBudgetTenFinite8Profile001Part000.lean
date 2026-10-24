import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile1_node2_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 115 19 228 232 16 32 64 128), lower := (rows 115 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 239 239 236 236 236 236 236 236) }] }

theorem profile1_node2 : Upper (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,17] 6 224 profile1_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,17] 6 224 profile1_node2_cert).mp (by decide +kernel))

def profile1_node3_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 115 50 197 201 16 32 64 128), lower := (rows 115 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 9 0 255 255 255), good := (rows 239 226 228 232 224 224 224 224) }] }

theorem profile1_node3 : Upper (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,48] 6 193 profile1_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,48] 6 193 profile1_node3_cert).mp (by decide +kernel))

def profile1_node4_cert : CutBound 8 := { lost := (rows 0 48 0 0 0 0 0 0), upper := (rows 115 131 244 248 16 32 64 128), lower := (rows 115 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 5, region := (rows 1 3 4 8 255 0 255 255), good := (rows 211 211 212 216 208 208 208 208) }] }

theorem profile1_node4 : Upper (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,129] 6 240 profile1_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,129] 6 240 profile1_node4_cert).mp (by decide +kernel))

def profile1_node5_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 115 146 229 233 16 32 64 128), lower := (rows 115 146 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 9 0 255 255 255), good := (rows 239 226 228 232 224 224 224 224) }] }

theorem profile1_node5 : Upper (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,144] 6 225 profile1_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114,144] 6 225 profile1_node5_cert).mp (by decide +kernel))

def profile1_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile1_node1_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node1 : Upper (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [114] 6 (by decide) (choices 2) [17,48,129,144] profile1_node1_route profile1_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node2
  · exact profile1_node3
  · exact profile1_node4
  · exact profile1_node5

def profile1_node7_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 241 19 230 234 16 32 64 128), lower := (rows 241 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 10 0 255 255 255), good := (rows 225 239 228 232 224 224 224 224) }] }

theorem profile1_node7 : Upper (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [240,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [240,17] 6 226 profile1_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [240,17] 6 226 profile1_node7_cert).mp (by decide +kernel))

def profile1_node8_cert : CutBound 8 := { lost := (rows 0 192 0 0 0 0 0 0), upper := (rows 241 50 199 203 16 32 64 128), lower := (rows 241 50 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 255 4 8 255 255 0 255), good := (rows 179 178 182 186 178 178 178 178) },{ target := 7, region := (rows 1 255 4 8 255 255 255 0), good := (rows 115 114 118 122 114 114 114 114) }] }

theorem profile1_node8 : Upper (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [240,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [240,48] 6 195 profile1_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [240,48] 6 195 profile1_node8_cert).mp (by decide +kernel))

def profile1_node6_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile1_node6_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile1_node6 : Upper (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [240] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [240] 6 (by decide) (choices 2) [17,48] profile1_node6_route profile1_node6_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node7
  · exact profile1_node8

def profile1_node0_column : Nat → Fin 8 := fun mask => match mask with | 30 => 2 | 46 => 2 | 78 => 2 | 142 => 2 | 54 => 2 | 86 => 2 | 150 => 2 | 102 => 2 | 166 => 2 | 198 => 2 | 58 => 3 | 90 => 3 | 154 => 3 | 106 => 3 | 170 => 3 | 202 => 3 | 60 => 2 | 92 => 2 | 156 => 2 | 108 => 2 | 172 => 2 | 204 => 2 | 116 => 2 | 180 => 2 | 212 => 2 | 228 => 2 | 120 => 3 | 184 => 3 | 216 => 3 | 232 => 3 | _ => 0

def profile1_node0_route : Route 8 := (fun mask => match mask with | 178 => (114,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 210 => (114,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 226 => (114,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node0 : Upper (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [] 6 (by decide) (choices 4) [114,240] profile1_node0_route profile1_node0_column
    (by change RowCover 8 4 (choices 4); exact cover ⟨4,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node1
  · exact profile1_node6

theorem profile1 : Upper (D (n:=8) [65,33,32,32,2,2,2,2]) (R (n:=8) [65,33,32,32,2,2,2,2]) [] 6 := profile1_node0


#print axioms profile1
end Delivery.SmallBudgetTenFinite8
