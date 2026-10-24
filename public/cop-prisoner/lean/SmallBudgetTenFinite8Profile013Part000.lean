import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile13_node3_cert : CutBound 8 := { lost := (rows 64 64 64 33 33 0 0 0), upper := (rows 7 35 37 200 208 32 64 128), lower := (rows 7 35 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 254 250 252 248 248 248 248 248) },{ target := 5, region := (rows 1 2 4 255 255 0 255 255), good := (rows 223 219 221 216 216 216 216 216) },{ target := 6, region := (rows 255 255 255 8 16 255 0 255), good := (rows 167 167 167 175 183 167 167 167) }] }

theorem profile13_node3 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,33] 6 192 profile13_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,33] 6 192 profile13_node3_cert).mp (by decide +kernel))

def profile13_node4_cert : CutBound 8 := { lost := (rows 96 64 32 1 1 0 0 0), upper := (rows 7 35 69 232 240 32 64 128), lower := (rows 7 35 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 254 250 252 248 248 248 248 248) },{ target := 5, region := (rows 3 2 7 8 16 0 255 255), good := (rows 199 199 197 200 208 192 192 192) },{ target := 6, region := (rows 5 7 4 8 16 255 0 255), good := (rows 167 163 167 168 176 160 160 160) }] }

theorem profile13_node4 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,65] 6 224 profile13_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,65] 6 224 profile13_node4_cert).mp (by decide +kernel))

def profile13_node5_cert : CutBound 8 := { lost := (rows 64 64 1 32 32 0 0 0), upper := (rows 7 35 100 201 209 32 64 128), lower := (rows 7 35 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 230 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 2 4 11 19 0 255 255), good := (rows 223 219 196 200 208 192 192 192) },{ target := 6, region := (rows 5 7 4 8 16 255 0 255), good := (rows 167 163 167 168 176 160 160 160) }] }

theorem profile13_node5 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,96] 6 193 profile13_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,96] 6 193 profile13_node5_cert).mp (by decide +kernel))

def profile13_node6_cert : CutBound 8 := { lost := (rows 96 64 33 0 0 0 0 0), upper := (rows 7 35 196 233 241 32 64 128), lower := (rows 7 35 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 230 230 228 236 244 228 228 228) },{ target := 5, region := (rows 3 2 255 8 16 0 255 255), good := (rows 199 199 196 204 212 196 196 196) },{ target := 6, region := (rows 5 7 4 8 16 255 0 255), good := (rows 167 163 167 168 176 160 160 160) }] }

theorem profile13_node6 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,192] 6 225 profile13_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33,192] 6 225 profile13_node6_cert).mp (by decide +kernel))

def profile13_node2_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node2_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile13_node2 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,33] 6 (by decide) (choices 2) [33,65,96,192] profile13_node2_route profile13_node2_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node3
  · exact profile13_node4
  · exact profile13_node5
  · exact profile13_node6

def profile13_node8_cert : CutBound 8 := { lost := (rows 64 1 64 32 32 0 0 0), upper := (rows 7 98 37 201 209 32 64 128), lower := (rows 7 98 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 230 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 4 13 21 0 255 255), good := (rows 223 194 221 200 208 192 192 192) },{ target := 6, region := (rows 3 2 7 8 16 255 0 255), good := (rows 167 167 165 168 176 160 160 160) }] }

theorem profile13_node8 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,33] 6 193 profile13_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,33] 6 193 profile13_node8_cert).mp (by decide +kernel))

def profile13_node9_cert : CutBound 8 := { lost := (rows 0 1 1 96 96 0 0 0), upper := (rows 7 98 100 137 145 32 64 128), lower := (rows 7 98 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 4 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) },{ target := 6, region := (rows 1 2 4 9 17 255 0 255), good := (rows 191 162 164 168 176 160 160 160) }] }

theorem profile13_node9 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,96] 6 129 profile13_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,96] 6 129 profile13_node9_cert).mp (by decide +kernel))

def profile13_node10_cert : CutBound 8 := { lost := (rows 96 1 96 0 0 0 0 0), upper := (rows 7 98 133 233 241 32 64 128), lower := (rows 7 98 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 230 226 230 234 242 226 226 226) },{ target := 5, region := (rows 3 2 7 8 16 0 255 255), good := (rows 199 199 197 200 208 192 192 192) },{ target := 6, region := (rows 3 2 7 8 16 255 0 255), good := (rows 167 167 165 168 176 160 160 160) }] }

theorem profile13_node10 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,129] 6 225 profile13_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,129] 6 225 profile13_node10_cert).mp (by decide +kernel))

def profile13_node11_cert : CutBound 8 := { lost := (rows 64 1 65 32 32 0 0 0), upper := (rows 7 98 164 201 209 32 64 128), lower := (rows 7 98 164 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 4 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 255 8 16 255 0 255), good := (rows 167 167 164 172 180 164 164 164) }] }

theorem profile13_node11 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,160] 6 193 profile13_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96,160] 6 193 profile13_node11_cert).mp (by decide +kernel))

def profile13_node7_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node7_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node7 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6,96] 6 (by decide) (choices 2) [33,96,129,160] profile13_node7_route profile13_node7_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node8
  · exact profile13_node9
  · exact profile13_node10
  · exact profile13_node11

def profile13_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node1_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node1 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [6] 6 (by decide) (choices 2) [33,96] profile13_node1_route profile13_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node2
  · exact profile13_node7

def profile13_node14_cert : CutBound 8 := { lost := (rows 0 32 0 33 33 0 0 0), upper := (rows 35 7 37 200 208 32 64 128), lower := (rows 35 7 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 250 254 252 248 248 248 248 248) },{ target := 5, region := (rows 1 6 4 255 255 0 255 255), good := (rows 219 223 223 216 216 216 216 216) }] }

theorem profile13_node14 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,33] 6 192 profile13_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,33] 6 192 profile13_node14_cert).mp (by decide +kernel))

def profile13_node15_cert : CutBound 8 := { lost := (rows 64 96 32 1 1 0 0 0), upper := (rows 35 7 69 232 240 32 64 128), lower := (rows 35 7 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 250 254 252 248 248 248 248 248) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 7 6 4 8 16 255 0 255), good := (rows 163 167 167 168 176 160 160 160) }] }

theorem profile13_node15 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,65] 6 224 profile13_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,65] 6 224 profile13_node15_cert).mp (by decide +kernel))

def profile13_node16_cert : CutBound 8 := { lost := (rows 64 64 1 32 32 0 0 0), upper := (rows 35 7 100 201 209 32 64 128), lower := (rows 35 7 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 230 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 2 4 11 19 0 255 255), good := (rows 219 223 196 200 208 192 192 192) },{ target := 6, region := (rows 7 6 4 8 16 255 0 255), good := (rows 163 167 167 168 176 160 160 160) }] }

theorem profile13_node16 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,96] 6 193 profile13_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,96] 6 193 profile13_node16_cert).mp (by decide +kernel))

def profile13_node17_cert : CutBound 8 := { lost := (rows 64 96 33 0 0 0 0 0), upper := (rows 35 7 196 233 241 32 64 128), lower := (rows 35 7 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 230 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 255 8 16 0 255 255), good := (rows 199 199 196 204 212 196 196 196) },{ target := 6, region := (rows 7 6 4 8 16 255 0 255), good := (rows 163 167 167 168 176 160 160 160) }] }

theorem profile13_node17 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,192] 6 225 profile13_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5,192] 6 225 profile13_node17_cert).mp (by decide +kernel))

def profile13_node13_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node13_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile13_node13 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,5] 6 (by decide) (choices 2) [33,65,96,192] profile13_node13_route profile13_node13_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node14
  · exact profile13_node15
  · exact profile13_node16
  · exact profile13_node17

def profile13_node18_cert : CutBound 8 := { lost := (rows 64 64 32 32 32 0 0 0), upper := (rows 35 35 197 205 213 32 64 128), lower := (rows 35 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 255 255), good := (rows 223 223 196 200 208 192 192 192) },{ target := 6, region := (rows 255 255 4 8 16 255 0 255), good := (rows 163 163 167 171 179 163 163 163) }] }

theorem profile13_node18 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,33] 6 197 profile13_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,33] 6 197 profile13_node18_cert).mp (by decide +kernel))

def profile13_node19_cert : CutBound 8 := { lost := (rows 64 65 32 32 32 0 0 0), upper := (rows 35 38 197 201 209 32 64 128), lower := (rows 35 38 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 16 255 255 255), good := (rows 226 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 198 196 200 208 192 192 192) },{ target := 6, region := (rows 7 6 4 8 16 255 0 255), good := (rows 163 167 167 168 176 160 160 160) }] }

theorem profile13_node19 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,36] 6 193 profile13_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,36] 6 193 profile13_node19_cert).mp (by decide +kernel))

def profile13_node21_cert : CutBound 8 := { lost := (rows 0 32 0 33 33 0 0 0), upper := (rows 35 67 37 204 212 32 64 128), lower := (rows 35 67 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 12 20 255 255 255), good := (rows 226 226 252 232 240 224 224 224) },{ target := 5, region := (rows 1 7 4 12 20 0 255 255), good := (rows 195 195 223 200 208 192 192 192) }] }

theorem profile13_node21 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,33] 6 196 profile13_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,33] 6 196 profile13_node21_cert).mp (by decide +kernel))

def profile13_node22_cert : CutBound 8 := { lost := (rows 64 32 32 65 65 0 0 0), upper := (rows 35 67 69 172 180 32 64 128), lower := (rows 35 67 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 12 20 255 255 255), good := (rows 226 226 252 232 240 224 224 224) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 12 20 255 0 255), good := (rows 163 163 189 168 176 160 160 160) }] }

theorem profile13_node22 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,65] 6 164 profile13_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,65] 6 164 profile13_node22_cert).mp (by decide +kernel))

def profile13_node23_cert : CutBound 8 := { lost := (rows 192 160 129 0 0 0 0 0), upper := (rows 35 67 100 141 149 32 64 128), lower := (rows 35 67 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 230 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 255 255 255 8 16 255 255 0), good := (rows 103 103 103 111 119 103 103 103) }] }

theorem profile13_node23 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,96] 6 133 profile13_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,96] 6 133 profile13_node23_cert).mp (by decide +kernel))

def profile13_node24_cert : CutBound 8 := { lost := (rows 64 32 96 1 1 0 0 0), upper := (rows 35 67 133 236 244 32 64 128), lower := (rows 35 67 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 12 20 255 255 255), good := (rows 226 226 252 232 240 224 224 224) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 3 2 7 8 16 255 0 255), good := (rows 167 167 165 168 176 160 160 160) }] }

theorem profile13_node24 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,129] 6 228 profile13_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,129] 6 228 profile13_node24_cert).mp (by decide +kernel))

def profile13_node25_cert : CutBound 8 := { lost := (rows 192 160 65 0 0 0 0 0), upper := (rows 35 67 164 205 213 32 64 128), lower := (rows 35 67 164 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 230 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 255 8 16 255 0 255), good := (rows 167 167 164 172 180 164 164 164) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile13_node25 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,160] 6 197 profile13_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,160] 6 197 profile13_node25_cert).mp (by decide +kernel))

def profile13_node26_cert : CutBound 8 := { lost := (rows 192 160 33 0 0 0 0 0), upper := (rows 35 67 196 173 181 32 64 128), lower := (rows 35 67 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 230 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 255 8 16 0 255 255), good := (rows 199 199 196 204 212 196 196 196) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile13_node26 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,192] 6 165 profile13_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65,192] 6 165 profile13_node26_cert).mp (by decide +kernel))

def profile13_node20_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node20_route : Route 8 := (fun mask => (mask,id))

theorem profile13_node20 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,65] 6 (by decide) (choices 2) [33,65,96,129,160,192] profile13_node20_route profile13_node20_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node21
  · exact profile13_node22
  · exact profile13_node23
  · exact profile13_node24
  · exact profile13_node25
  · exact profile13_node26

def profile13_node27_cert : CutBound 8 := { lost := (rows 192 161 0 0 0 0 0 0), upper := (rows 35 70 229 233 241 32 64 128), lower := (rows 35 70 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 16 255 255 255), good := (rows 226 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 6 4 8 16 0 255 255), good := (rows 195 198 198 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 167 164 168 176 160 160 160) },{ target := 7, region := (rows 7 6 4 8 16 255 255 0), good := (rows 99 103 103 104 112 96 96 96) }] }

theorem profile13_node27 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,68] 6 225 profile13_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,68] 6 225 profile13_node27_cert).mp (by decide +kernel))

def profile13_node28_cert : CutBound 8 := { lost := (rows 64 1 32 32 32 0 0 0), upper := (rows 35 98 197 205 213 32 64 128), lower := (rows 35 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) }] }

theorem profile13_node28 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,96] 6 197 profile13_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,96] 6 197 profile13_node28_cert).mp (by decide +kernel))

def profile13_node30_cert : CutBound 8 := { lost := (rows 64 33 64 32 32 0 0 0), upper := (rows 35 194 37 205 213 32 64 128), lower := (rows 35 194 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 255 4 12 20 0 255 255), good := (rows 195 194 223 202 210 194 194 194) },{ target := 6, region := (rows 3 2 7 8 16 255 0 255), good := (rows 167 167 165 168 176 160 160 160) }] }

theorem profile13_node30 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,33] 6 197 profile13_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,33] 6 197 profile13_node30_cert).mp (by decide +kernel))

def profile13_node31_cert : CutBound 8 := { lost := (rows 64 33 32 64 64 0 0 0), upper := (rows 35 194 69 173 181 32 64 128), lower := (rows 35 194 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 199 194 199 202 210 194 194 194) },{ target := 6, region := (rows 3 2 4 12 20 255 0 255), good := (rows 163 163 189 168 176 160 160 160) }] }

theorem profile13_node31 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,65] 6 165 profile13_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,65] 6 165 profile13_node31_cert).mp (by decide +kernel))

def profile13_node32_cert : CutBound 8 := { lost := (rows 192 33 129 0 0 0 0 0), upper := (rows 35 194 100 141 149 32 64 128), lower := (rows 35 194 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 255 4 8 16 0 255 255), good := (rows 195 194 198 202 210 194 194 194) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 3 2 255 8 16 255 255 0), good := (rows 103 103 100 108 116 100 100 100) }] }

theorem profile13_node32 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,96] 6 133 profile13_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,96] 6 133 profile13_node32_cert).mp (by decide +kernel))

def profile13_node33_cert : CutBound 8 := { lost := (rows 64 33 33 0 0 0 0 0), upper := (rows 35 194 196 45 53 32 64 128), lower := (rows 35 194 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 255 255 8 16 0 255 255), good := (rows 199 198 198 206 214 198 198 198) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) }] }

theorem profile13_node33 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,192] 6 37 profile13_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192,192] 6 37 profile13_node33_cert).mp (by decide +kernel))

def profile13_node29_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node29_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile13_node29 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34,192] 6 (by decide) (choices 2) [33,65,96,192] profile13_node29_route profile13_node29_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node30
  · exact profile13_node31
  · exact profile13_node32
  · exact profile13_node33

def profile13_node12_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node12_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile13_node12 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [34] 6 (by decide) (choices 2) [5,33,36,65,68,96,192] profile13_node12_route profile13_node12_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node13
  · exact profile13_node18
  · exact profile13_node19
  · exact profile13_node20
  · exact profile13_node27
  · exact profile13_node28
  · exact profile13_node29

def profile13_node36_cert : CutBound 8 := { lost := (rows 0 96 96 1 1 0 0 0), upper := (rows 97 7 7 232 240 32 64 128), lower := (rows 97 7 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 254 254 248 248 248 248 248) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 1 7 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile13_node36 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,3] 6 224 profile13_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,3] 6 224 profile13_node36_cert).mp (by decide +kernel))

def profile13_node37_cert : CutBound 8 := { lost := (rows 0 32 0 33 33 0 0 0), upper := (rows 97 7 37 202 210 32 64 128), lower := (rows 97 7 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 255 255 255), good := (rows 224 254 228 232 240 224 224 224) },{ target := 5, region := (rows 1 6 4 14 22 0 255 255), good := (rows 193 223 223 200 208 192 192 192) }] }

theorem profile13_node37 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,33] 6 194 profile13_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,33] 6 194 profile13_node37_cert).mp (by decide +kernel))

def profile13_node38_cert : CutBound 8 := { lost := (rows 0 64 65 32 32 0 0 0), upper := (rows 97 7 38 201 209 32 64 128), lower := (rows 97 7 38 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 2 4 11 19 0 255 255), good := (rows 217 223 222 200 208 192 192 192) },{ target := 6, region := (rows 1 3 7 8 16 255 0 255), good := (rows 167 167 166 168 176 160 160 160) }] }

theorem profile13_node38 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,34] 6 193 profile13_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,34] 6 193 profile13_node38_cert).mp (by decide +kernel))

def profile13_node39_cert : CutBound 8 := { lost := (rows 0 0 1 96 96 0 0 0), upper := (rows 97 7 100 139 147 32 64 128), lower := (rows 97 7 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 228 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 2 4 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) },{ target := 6, region := (rows 1 2 4 10 18 255 0 255), good := (rows 161 191 164 168 176 160 160 160) }] }

theorem profile13_node39 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,96] 6 131 profile13_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,96] 6 131 profile13_node39_cert).mp (by decide +kernel))

def profile13_node40_cert : CutBound 8 := { lost := (rows 0 96 96 1 1 0 0 0), upper := (rows 97 7 133 234 242 32 64 128), lower := (rows 97 7 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 255 255 255), good := (rows 224 254 228 232 240 224 224 224) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 1 7 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile13_node40 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,129] 6 226 profile13_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,129] 6 226 profile13_node40_cert).mp (by decide +kernel))

def profile13_node41_cert : CutBound 8 := { lost := (rows 0 96 97 0 0 0 0 0), upper := (rows 97 7 134 233 241 32 64 128), lower := (rows 97 7 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 3 7 8 16 0 255 255), good := (rows 199 199 198 200 208 192 192 192) },{ target := 6, region := (rows 1 3 7 8 16 255 0 255), good := (rows 167 167 166 168 176 160 160 160) }] }

theorem profile13_node41 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,130] 6 225 profile13_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,130] 6 225 profile13_node41_cert).mp (by decide +kernel))

def profile13_node42_cert : CutBound 8 := { lost := (rows 0 64 65 32 32 0 0 0), upper := (rows 97 7 164 203 211 32 64 128), lower := (rows 97 7 164 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 228 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 2 4 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 255 8 16 255 0 255), good := (rows 167 167 164 172 180 164 164 164) }] }

theorem profile13_node42 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,160] 6 195 profile13_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5,160] 6 195 profile13_node42_cert).mp (by decide +kernel))

def profile13_node35_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node35_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node35 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,5] 6 (by decide) (choices 2) [3,33,34,96,129,130,160] profile13_node35_route profile13_node35_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node36
  · exact profile13_node37
  · exact profile13_node38
  · exact profile13_node39
  · exact profile13_node40
  · exact profile13_node41
  · exact profile13_node42

def profile13_node43_cert : CutBound 8 := { lost := (rows 128 192 32 32 32 0 0 0), upper := (rows 97 35 199 207 215 32 64 128), lower := (rows 97 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile13_node43 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,33] 6 199 profile13_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,33] 6 199 profile13_node43_cert).mp (by decide +kernel))

def profile13_node45_cert : CutBound 8 := { lost := (rows 0 65 64 32 32 0 0 0), upper := (rows 97 38 7 201 209 32 64 128), lower := (rows 97 38 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 2 4 13 21 0 255 255), good := (rows 217 222 223 200 208 192 192 192) },{ target := 6, region := (rows 1 7 5 8 16 255 0 255), good := (rows 167 166 167 168 176 160 160 160) }] }

theorem profile13_node45 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,3] 6 193 profile13_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,3] 6 193 profile13_node45_cert).mp (by decide +kernel))

def profile13_node46_cert : CutBound 8 := { lost := (rows 0 65 32 64 64 0 0 0), upper := (rows 97 38 69 139 147 32 64 128), lower := (rows 97 38 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 198 197 200 208 192 192 192) },{ target := 6, region := (rows 1 6 4 12 20 255 0 255), good := (rows 161 190 191 168 176 160 160 160) }] }

theorem profile13_node46 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,65] 6 131 profile13_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,65] 6 131 profile13_node46_cert).mp (by decide +kernel))

def profile13_node47_cert : CutBound 8 := { lost := (rows 0 1 33 32 32 0 0 0), upper := (rows 97 38 70 137 145 32 64 128), lower := (rows 97 38 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 6 9 17 0 255 255), good := (rows 217 198 198 200 208 192 192 192) }] }

theorem profile13_node47 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,66] 6 129 profile13_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,66] 6 129 profile13_node47_cert).mp (by decide +kernel))

def profile13_node48_cert : CutBound 8 := { lost := (rows 128 193 96 0 0 0 0 0), upper := (rows 97 38 133 203 211 32 64 128), lower := (rows 97 38 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 198 197 200 208 192 192 192) },{ target := 6, region := (rows 1 7 5 8 16 255 0 255), good := (rows 167 166 167 168 176 160 160 160) },{ target := 7, region := (rows 255 6 4 8 16 255 255 0), good := (rows 97 103 103 105 113 97 97 97) }] }

theorem profile13_node48 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,129] 6 195 profile13_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,129] 6 195 profile13_node48_cert).mp (by decide +kernel))

def profile13_node49_cert : CutBound 8 := { lost := (rows 0 1 33 32 32 0 0 0), upper := (rows 97 38 134 201 209 32 64 128), lower := (rows 97 38 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 6 9 17 0 255 255), good := (rows 217 198 198 200 208 192 192 192) }] }

theorem profile13_node49 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,130] 6 193 profile13_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,130] 6 193 profile13_node49_cert).mp (by decide +kernel))

def profile13_node50_cert : CutBound 8 := { lost := (rows 128 193 33 0 0 0 0 0), upper := (rows 97 38 196 139 147 32 64 128), lower := (rows 97 38 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 255 8 16 0 255 255), good := (rows 197 198 196 204 212 196 196 196) },{ target := 6, region := (rows 1 6 4 8 16 255 0 255), good := (rows 161 166 166 168 176 160 160 160) },{ target := 7, region := (rows 255 6 4 8 16 255 255 0), good := (rows 97 103 103 105 113 97 97 97) }] }

theorem profile13_node50 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,192] 6 131 profile13_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36,192] 6 131 profile13_node50_cert).mp (by decide +kernel))

def profile13_node44_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile13_node44_route : Route 8 := (fun mask => (mask,id))

theorem profile13_node44 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,36] 6 (by decide) (choices 2) [3,65,66,129,130,192] profile13_node44_route profile13_node44_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node45
  · exact profile13_node46
  · exact profile13_node47
  · exact profile13_node48
  · exact profile13_node49
  · exact profile13_node50

def profile13_node52_cert : CutBound 8 := { lost := (rows 0 1 0 96 96 0 0 0), upper := (rows 97 98 7 141 149 32 64 128), lower := (rows 97 98 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 4 12 20 0 255 255), good := (rows 193 194 223 200 208 192 192 192) },{ target := 6, region := (rows 1 2 4 12 20 255 0 255), good := (rows 161 162 191 168 176 160 160 160) }] }

theorem profile13_node52 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,96,3] 6 133 profile13_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,96,3] 6 133 profile13_node52_cert).mp (by decide +kernel))

def profile13_node53_cert : CutBound 8 := { lost := (rows 128 129 96 0 0 0 0 0), upper := (rows 97 98 133 143 151 32 64 128), lower := (rows 97 98 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 2 5 8 16 255 0 255), good := (rows 165 162 165 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile13_node53 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,96,129] 6 135 profile13_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,96,129] 6 135 profile13_node53_cert).mp (by decide +kernel))

def profile13_node54_cert : CutBound 8 := { lost := (rows 128 129 97 0 0 0 0 0), upper := (rows 97 98 134 141 149 32 64 128), lower := (rows 97 98 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 6 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 2 6 8 16 255 0 255), good := (rows 161 166 166 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile13_node54 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,96,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,96,130] 6 133 profile13_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,96,130] 6 133 profile13_node54_cert).mp (by decide +kernel))

def profile13_node51_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 65 => 6 | 10 => 3 | 18 => 4 | 34 => 5 | 66 => 6 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile13_node51_route : Route 8 := (fun mask => (mask,id))

theorem profile13_node51 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,96] 6 (by decide) (choices 2) [3,129,130] profile13_node51_route profile13_node51_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node52
  · exact profile13_node53
  · exact profile13_node54

def profile13_node56_cert : CutBound 8 := { lost := (rows 0 96 96 1 1 0 0 0), upper := (rows 97 131 7 236 244 32 64 128), lower := (rows 97 131 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 12 20 255 255 255), good := (rows 224 226 254 232 240 224 224 224) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 1 7 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile13_node56 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,3] 6 228 profile13_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,3] 6 228 profile13_node56_cert).mp (by decide +kernel))

def profile13_node57_cert : CutBound 8 := { lost := (rows 0 96 64 32 32 0 0 0), upper := (rows 97 131 37 206 214 32 64 128), lower := (rows 97 131 37 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 7 4 12 20 0 255 255), good := (rows 195 195 223 200 208 192 192 192) },{ target := 6, region := (rows 1 7 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile13_node57 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,33] 6 198 profile13_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,33] 6 198 profile13_node57_cert).mp (by decide +kernel))

def profile13_node58_cert : CutBound 8 := { lost := (rows 128 96 193 0 0 0 0 0), upper := (rows 97 131 38 205 213 32 64 128), lower := (rows 97 131 38 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 198 200 208 192 192 192) },{ target := 6, region := (rows 1 3 7 8 16 255 0 255), good := (rows 167 167 166 168 176 160 160 160) },{ target := 7, region := (rows 255 2 6 8 16 255 255 0), good := (rows 97 103 103 105 113 97 97 97) }] }

theorem profile13_node58 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,34] 6 197 profile13_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,34] 6 197 profile13_node58_cert).mp (by decide +kernel))

def profile13_node59_cert : CutBound 8 := { lost := (rows 128 96 129 0 0 0 0 0), upper := (rows 97 131 100 143 151 32 64 128), lower := (rows 97 131 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 228 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 255 2 255 8 16 255 255 0), good := (rows 101 103 101 109 117 101 101 101) }] }

theorem profile13_node59 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,96] 6 135 profile13_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,96] 6 135 profile13_node59_cert).mp (by decide +kernel))

def profile13_node60_cert : CutBound 8 := { lost := (rows 128 96 96 0 0 0 0 0), upper := (rows 97 131 133 110 118 32 64 128), lower := (rows 97 131 133 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 1 7 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) },{ target := 7, region := (rows 255 2 4 8 16 255 255 0), good := (rows 97 99 101 105 113 97 97 97) }] }

theorem profile13_node60 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,129] 6 102 profile13_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,129] 6 102 profile13_node60_cert).mp (by decide +kernel))

def profile13_node61_cert : CutBound 8 := { lost := (rows 0 96 97 0 0 0 0 0), upper := (rows 97 131 134 109 117 32 64 128), lower := (rows 97 131 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 3 7 8 16 0 255 255), good := (rows 199 199 198 200 208 192 192 192) },{ target := 6, region := (rows 1 3 7 8 16 255 0 255), good := (rows 167 167 166 168 176 160 160 160) }] }

theorem profile13_node61 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,130] 6 101 profile13_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,130] 6 101 profile13_node61_cert).mp (by decide +kernel))

def profile13_node62_cert : CutBound 8 := { lost := (rows 128 96 65 0 0 0 0 0), upper := (rows 97 131 164 79 87 32 64 128), lower := (rows 97 131 164 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 228 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 255 8 16 255 0 255), good := (rows 167 167 164 172 180 164 164 164) },{ target := 7, region := (rows 255 2 4 8 16 255 255 0), good := (rows 97 99 101 105 113 97 97 97) }] }

theorem profile13_node62 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,160] 6 71 profile13_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129,160] 6 71 profile13_node62_cert).mp (by decide +kernel))

def profile13_node55_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node55_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node55 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,129] 6 (by decide) (choices 2) [3,33,34,96,129,130,160] profile13_node55_route profile13_node55_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node56
  · exact profile13_node57
  · exact profile13_node58
  · exact profile13_node59
  · exact profile13_node60
  · exact profile13_node61
  · exact profile13_node62

def profile13_node64_cert : CutBound 8 := { lost := (rows 0 97 96 0 0 0 0 0), upper := (rows 97 134 7 233 241 32 64 128), lower := (rows 97 134 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 7 5 8 16 0 255 255), good := (rows 199 198 199 200 208 192 192 192) },{ target := 6, region := (rows 1 7 5 8 16 255 0 255), good := (rows 167 166 167 168 176 160 160 160) }] }

theorem profile13_node64 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,3] 6 225 profile13_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,3] 6 225 profile13_node64_cert).mp (by decide +kernel))

def profile13_node65_cert : CutBound 8 := { lost := (rows 0 97 64 32 32 0 0 0), upper := (rows 97 134 37 203 211 32 64 128), lower := (rows 97 134 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 6 4 12 20 0 255 255), good := (rows 193 222 223 200 208 192 192 192) },{ target := 6, region := (rows 1 7 5 8 16 255 0 255), good := (rows 167 166 167 168 176 160 160 160) }] }

theorem profile13_node65 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,33] 6 195 profile13_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,33] 6 195 profile13_node65_cert).mp (by decide +kernel))

def profile13_node66_cert : CutBound 8 := { lost := (rows 0 33 1 32 32 0 0 0), upper := (rows 97 134 38 201 209 32 64 128), lower := (rows 97 134 38 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 6 4 9 17 0 255 255), good := (rows 217 198 198 200 208 192 192 192) }] }

theorem profile13_node66 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,34] 6 193 profile13_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,34] 6 193 profile13_node66_cert).mp (by decide +kernel))

def profile13_node67_cert : CutBound 8 := { lost := (rows 128 97 129 0 0 0 0 0), upper := (rows 97 134 100 139 147 32 64 128), lower := (rows 97 134 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 6 4 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 6 4 8 16 255 0 255), good := (rows 161 166 166 168 176 160 160 160) },{ target := 7, region := (rows 255 2 255 8 16 255 255 0), good := (rows 101 103 101 109 117 101 101 101) }] }

theorem profile13_node67 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,96] 6 131 profile13_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,96] 6 131 profile13_node67_cert).mp (by decide +kernel))

def profile13_node68_cert : CutBound 8 := { lost := (rows 0 97 96 0 0 0 0 0), upper := (rows 97 134 133 107 115 32 64 128), lower := (rows 97 134 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 7 5 8 16 0 255 255), good := (rows 199 198 199 200 208 192 192 192) },{ target := 6, region := (rows 1 7 5 8 16 255 0 255), good := (rows 167 166 167 168 176 160 160 160) }] }

theorem profile13_node68 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,129] 6 99 profile13_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,129] 6 99 profile13_node68_cert).mp (by decide +kernel))

def profile13_node69_cert : CutBound 8 := { lost := (rows 0 97 97 0 0 0 0 0), upper := (rows 97 134 134 105 113 32 64 128), lower := (rows 97 134 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 255 255 8 16 0 255 255), good := (rows 199 198 198 206 214 198 198 198) },{ target := 6, region := (rows 1 255 255 8 16 255 0 255), good := (rows 167 166 166 174 182 166 166 166) }] }

theorem profile13_node69 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,130] 6 97 profile13_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,130] 6 97 profile13_node69_cert).mp (by decide +kernel))

def profile13_node70_cert : CutBound 8 := { lost := (rows 0 97 65 0 0 0 0 0), upper := (rows 97 134 164 75 83 32 64 128), lower := (rows 97 134 164 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 6 4 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 255 255 8 16 255 0 255), good := (rows 167 166 166 174 182 166 166 166) }] }

theorem profile13_node70 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,160] 6 67 profile13_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132,160] 6 67 profile13_node70_cert).mp (by decide +kernel))

def profile13_node63_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node63_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node63 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,132] 6 (by decide) (choices 2) [3,33,34,96,129,130,160] profile13_node63_route profile13_node63_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node64
  · exact profile13_node65
  · exact profile13_node66
  · exact profile13_node67
  · exact profile13_node68
  · exact profile13_node69
  · exact profile13_node70

def profile13_node72_cert : CutBound 8 := { lost := (rows 0 65 64 32 32 0 0 0), upper := (rows 97 162 7 205 213 32 64 128), lower := (rows 97 162 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 4 12 20 0 255 255), good := (rows 193 194 223 200 208 192 192 192) },{ target := 6, region := (rows 1 255 5 8 16 255 0 255), good := (rows 167 162 167 170 178 162 162 162) }] }

theorem profile13_node72 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,3] 6 197 profile13_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,3] 6 197 profile13_node72_cert).mp (by decide +kernel))

def profile13_node73_cert : CutBound 8 := { lost := (rows 0 65 32 64 64 0 0 0), upper := (rows 97 162 69 143 151 32 64 128), lower := (rows 97 162 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 255 4 12 20 255 0 255), good := (rows 163 162 191 170 178 162 162 162) }] }

theorem profile13_node73 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,65] 6 135 profile13_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,65] 6 135 profile13_node73_cert).mp (by decide +kernel))

def profile13_node74_cert : CutBound 8 := { lost := (rows 128 65 161 0 0 0 0 0), upper := (rows 97 162 70 141 149 32 64 128), lower := (rows 97 162 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 6 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 255 4 8 16 255 0 255), good := (rows 163 162 166 170 178 162 162 162) },{ target := 7, region := (rows 255 2 6 8 16 255 255 0), good := (rows 97 103 103 105 113 97 97 97) }] }

theorem profile13_node74 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,66] 6 133 profile13_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,66] 6 133 profile13_node74_cert).mp (by decide +kernel))

def profile13_node75_cert : CutBound 8 := { lost := (rows 128 65 96 0 0 0 0 0), upper := (rows 97 162 133 79 87 32 64 128), lower := (rows 97 162 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 255 5 8 16 255 0 255), good := (rows 167 162 167 170 178 162 162 162) },{ target := 7, region := (rows 255 2 4 8 16 255 255 0), good := (rows 97 99 101 105 113 97 97 97) }] }

theorem profile13_node75 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,129] 6 71 profile13_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,129] 6 71 profile13_node75_cert).mp (by decide +kernel))

def profile13_node76_cert : CutBound 8 := { lost := (rows 0 65 97 0 0 0 0 0), upper := (rows 97 162 134 77 85 32 64 128), lower := (rows 97 162 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 6 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 255 255 8 16 255 0 255), good := (rows 167 166 166 174 182 166 166 166) }] }

theorem profile13_node76 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,130] 6 69 profile13_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,130] 6 69 profile13_node76_cert).mp (by decide +kernel))

def profile13_node77_cert : CutBound 8 := { lost := (rows 128 65 33 0 0 0 0 0), upper := (rows 97 162 196 15 23 32 64 128), lower := (rows 97 162 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 255 8 16 0 255 255), good := (rows 197 198 196 204 212 196 196 196) },{ target := 6, region := (rows 1 255 4 8 16 255 0 255), good := (rows 163 162 166 170 178 162 162 162) },{ target := 7, region := (rows 255 2 4 8 16 255 255 0), good := (rows 97 99 101 105 113 97 97 97) }] }

theorem profile13_node77 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,192] 6 7 profile13_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160,192] 6 7 profile13_node77_cert).mp (by decide +kernel))

def profile13_node71_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile13_node71_route : Route 8 := (fun mask => (mask,id))

theorem profile13_node71 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96,160] 6 (by decide) (choices 2) [3,65,66,129,130,192] profile13_node71_route profile13_node71_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node72
  · exact profile13_node73
  · exact profile13_node74
  · exact profile13_node75
  · exact profile13_node76
  · exact profile13_node77

def profile13_node34_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node34_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node34 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [96] 6 (by decide) (choices 2) [5,33,36,96,129,132,160] profile13_node34_route profile13_node34_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node35
  · exact profile13_node43
  · exact profile13_node44
  · exact profile13_node51
  · exact profile13_node55
  · exact profile13_node63
  · exact profile13_node71

def profile13_node0_column : Nat → Fin 8 := fun mask => match mask with | 10 => 3 | 18 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile13_node0_route : Route 8 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 68 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 132 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node0 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [] 6 (by decide) (choices 2) [6,34,96] profile13_node0_route profile13_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node1
  · exact profile13_node12
  · exact profile13_node34

theorem profile13 : Upper (D (n:=8) [34,33,33,32,32,2,2,2]) (R (n:=8) [34,33,33,32,32,2,2,2]) [] 6 := profile13_node0


#print axioms profile13
end Delivery.SmallBudgetTenFinite8
