import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile9_node2_cert : CutBound 8 := { lost := (rows 0 96 0 0 0 0 0 0), upper := (rows 113 19 244 248 240 32 64 128), lower := (rows 113 19 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 211 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 179 179 164 168 176 160 160 160) }] }

theorem profile9_node2 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,17] 6 240 profile9_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,17] 6 240 profile9_node2_cert).mp (by decide +kernel))

def profile9_node3_cert : CutBound 8 := { lost := (rows 0 16 32 32 0 0 0 0), upper := (rows 113 35 212 216 208 32 64 128), lower := (rows 113 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 221 223 220 220 220 220 220 220) }] }

theorem profile9_node3 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,33] 6 208 profile9_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,33] 6 208 profile9_node3_cert).mp (by decide +kernel))

def profile9_node4_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 113 50 213 217 209 32 64 128), lower := (rows 113 50 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 210 196 200 208 192 192 192) }] }

theorem profile9_node4 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,48] 6 209 profile9_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,48] 6 209 profile9_node4_cert).mp (by decide +kernel))

def profile9_node5_cert : CutBound 8 := { lost := (rows 0 16 32 32 0 0 0 0), upper := (rows 113 98 149 153 145 32 64 128), lower := (rows 113 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 255 255 255), good := (rows 227 226 230 234 226 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 194 196 200 208 192 192 192) }] }

theorem profile9_node5 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,96] 6 145 profile9_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,96] 6 145 profile9_node5_cert).mp (by decide +kernel))

def profile9_node6_cert : CutBound 8 := { lost := (rows 0 48 0 0 0 0 0 0), upper := (rows 113 131 244 248 240 32 64 128), lower := (rows 113 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 195 196 200 208 192 192 192) }] }

theorem profile9_node6 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,129] 6 240 profile9_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,129] 6 240 profile9_node6_cert).mp (by decide +kernel))

def profile9_node7_cert : CutBound 8 := { lost := (rows 0 96 0 0 0 0 0 0), upper := (rows 113 146 245 249 241 32 64 128), lower := (rows 113 146 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 19 4 8 16 0 255 255), good := (rows 211 210 196 200 210 192 192 192) },{ target := 6, region := (rows 1 19 4 8 16 255 0 255), good := (rows 179 178 164 168 178 160 160 160) }] }

theorem profile9_node7 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,144] 6 241 profile9_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,144] 6 241 profile9_node7_cert).mp (by decide +kernel))

def profile9_node8_cert : CutBound 8 := { lost := (rows 0 16 32 32 0 0 0 0), upper := (rows 113 162 213 217 209 32 64 128), lower := (rows 113 162 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 255 255 255), good := (rows 227 226 230 234 226 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 194 196 200 208 192 192 192) }] }

theorem profile9_node8 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,160] 6 209 profile9_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112,160] 6 209 profile9_node8_cert).mp (by decide +kernel))

def profile9_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile9_node1_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile9_node1 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [112] 6 (by decide) (choices 2) [17,33,48,96,129,144,160] profile9_node1_route profile9_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node2
  · exact profile9_node3
  · exact profile9_node4
  · exact profile9_node5
  · exact profile9_node6
  · exact profile9_node7
  · exact profile9_node8

def profile9_node11_cert : CutBound 8 := { lost := (rows 16 32 0 32 0 0 0 0), upper := (rows 225 19 52 216 208 32 64 128), lower := (rows 225 19 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 255 255 255), good := (rows 225 227 229 233 225 225 225 225) },{ target := 5, region := (rows 1 3 4 255 255 0 255 255), good := (rows 219 219 220 216 216 216 216 216) }] }

theorem profile9_node11 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,17,48] 6 208 profile9_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,17,48] 6 208 profile9_node11_cert).mp (by decide +kernel))

def profile9_node12_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 225 19 100 152 144 32 64 128), lower := (rows 225 19 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 255 255 255), good := (rows 229 231 229 237 229 229 229 229) }] }

theorem profile9_node12 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,17,96] 6 144 profile9_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,17,96] 6 144 profile9_node12_cert).mp (by decide +kernel))

def profile9_node10_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile9_node10_route : Route 8 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile9_node10 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,17] 6 (by decide) (choices 2) [48,96] profile9_node10_route profile9_node10_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node11
  · exact profile9_node12

def profile9_node13_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 225 35 212 216 208 32 64 128), lower := (rows 225 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) }] }

theorem profile9_node13 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,33] 6 208 profile9_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,33] 6 208 profile9_node13_cert).mp (by decide +kernel))

def profile9_node14_cert : CutBound 8 := { lost := (rows 16 0 32 32 0 0 0 0), upper := (rows 225 50 213 217 209 32 64 128), lower := (rows 225 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 255 255 255), good := (rows 225 227 229 233 225 225 225 225) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 210 196 200 208 192 192 192) }] }

theorem profile9_node14 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,48] 6 209 profile9_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,48] 6 209 profile9_node14_cert).mp (by decide +kernel))

def profile9_node15_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 225 98 149 153 145 32 64 128), lower := (rows 225 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) }] }

theorem profile9_node15 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,96] 6 145 profile9_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224,96] 6 145 profile9_node15_cert).mp (by decide +kernel))

def profile9_node9_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile9_node9_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile9_node9 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [224] 6 (by decide) (choices 2) [17,33,48,96] profile9_node9_route profile9_node9_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile9_node10
  · exact profile9_node13
  · exact profile9_node14
  · exact profile9_node15

def profile9_node0_column : Nat → Fin 8 := fun mask => match mask with | 14 => 1 | 22 => 1 | 38 => 1 | 70 => 1 | 134 => 1 | 26 => 1 | 42 => 1 | 74 => 1 | 138 => 1 | 50 => 1 | 82 => 1 | 146 => 1 | 98 => 1 | 162 => 1 | 194 => 1 | 28 => 2 | 44 => 2 | 76 => 2 | 140 => 2 | 52 => 2 | 84 => 2 | 148 => 2 | 100 => 2 | 164 => 2 | 196 => 2 | 56 => 3 | 88 => 3 | 152 => 3 | 104 => 3 | 168 => 3 | 200 => 3 | _ => 0

def profile9_node0_route : Route 8 := (fun mask => match mask with | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile9_node0 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [] 6 (by decide) (choices 3) [112,224] profile9_node0_route profile9_node0_column
    (by change RowCover 8 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node1
  · exact profile9_node9

theorem profile9 : Upper (D (n:=8) [49,32,32,32,19,2,2,2]) (R (n:=8) [49,32,32,32,19,2,2,2]) [] 6 := profile9_node0


#print axioms profile9
end Delivery.SmallBudgetTenFinite8
