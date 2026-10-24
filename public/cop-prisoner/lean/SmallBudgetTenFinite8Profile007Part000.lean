import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile7_node2_cert : CutBound 8 := { lost := (rows 0 96 16 16 0 0 0 0), upper := (rows 113 19 229 233 241 32 64 128), lower := (rows 113 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 7 11 0 255 255 255), good := (rows 237 239 228 232 224 224 224 224) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 211 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 179 179 164 168 176 160 160 160) }] }

theorem profile7_node2 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,17] 6 225 profile7_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,17] 6 225 profile7_node2_cert).mp (by decide +kernel))

def profile7_node3_cert : CutBound 8 := { lost := (rows 0 80 32 32 0 0 0 0), upper := (rows 113 35 213 217 209 32 64 128), lower := (rows 113 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 5, region := (rows 1 2 7 11 19 0 255 255), good := (rows 221 223 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 179 163 164 168 176 160 160 160) }] }

theorem profile7_node3 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,33] 6 209 profile7_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,33] 6 209 profile7_node3_cert).mp (by decide +kernel))

def profile7_node4_cert : CutBound 8 := { lost := (rows 0 1 48 48 0 0 0 0), upper := (rows 113 50 197 201 209 32 64 128), lower := (rows 113 50 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 255 255 255), good := (rows 242 242 228 232 242 224 224 224) },{ target := 4, region := (rows 1 2 5 9 0 255 255 255), good := (rows 237 226 228 232 224 224 224 224) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 210 196 200 208 192 192 192) }] }

theorem profile7_node4 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,48] 6 193 profile7_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,48] 6 193 profile7_node4_cert).mp (by decide +kernel))

def profile7_node5_cert : CutBound 8 := { lost := (rows 0 17 32 32 0 0 0 0), upper := (rows 113 98 149 153 145 32 64 128), lower := (rows 113 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 242 226 230 234 242 226 226 226) },{ target := 4, region := (rows 1 255 4 8 0 255 255 255), good := (rows 227 226 230 234 226 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 194 196 200 208 192 192 192) }] }

theorem profile7_node5 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,96] 6 145 profile7_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,96] 6 145 profile7_node5_cert).mp (by decide +kernel))

def profile7_node6_cert : CutBound 8 := { lost := (rows 128 112 0 0 0 0 0 0), upper := (rows 113 131 245 249 241 32 64 128), lower := (rows 113 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 195 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 179 163 164 168 176 160 160 160) },{ target := 7, region := (rows 17 2 4 8 16 255 255 0), good := (rows 113 99 100 104 113 96 96 96) }] }

theorem profile7_node6 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,129] 6 241 profile7_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,129] 6 241 profile7_node6_cert).mp (by decide +kernel))

def profile7_node7_cert : CutBound 8 := { lost := (rows 0 33 16 16 0 0 0 0), upper := (rows 113 146 229 233 241 32 64 128), lower := (rows 113 146 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 255 255 255), good := (rows 242 242 228 232 242 224 224 224) },{ target := 4, region := (rows 1 2 5 9 0 255 255 255), good := (rows 237 226 228 232 224 224 224 224) },{ target := 5, region := (rows 1 19 4 8 16 0 255 255), good := (rows 211 210 196 200 210 192 192 192) }] }

theorem profile7_node7 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,144] 6 225 profile7_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,144] 6 225 profile7_node7_cert).mp (by decide +kernel))

def profile7_node8_cert : CutBound 8 := { lost := (rows 0 17 32 32 0 0 0 0), upper := (rows 113 162 213 217 209 32 64 128), lower := (rows 113 162 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 242 226 230 234 242 226 226 226) },{ target := 4, region := (rows 1 255 4 8 0 255 255 255), good := (rows 227 226 230 234 226 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 194 196 200 208 192 192 192) }] }

theorem profile7_node8 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,160] 6 209 profile7_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112,160] 6 209 profile7_node8_cert).mp (by decide +kernel))

def profile7_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile7_node1_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile7_node1 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [112] 6 (by decide) (choices 2) [17,33,48,96,129,144,160] profile7_node1_route profile7_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node2
  · exact profile7_node3
  · exact profile7_node4
  · exact profile7_node5
  · exact profile7_node6
  · exact profile7_node7
  · exact profile7_node8

def profile7_node11_cert : CutBound 8 := { lost := (rows 16 32 32 17 0 0 0 0), upper := (rows 225 19 21 232 240 32 64 128), lower := (rows 225 19 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 1 6 6 8 16 0 255 255), good := (rows 193 215 215 200 208 192 192 192) }] }

theorem profile7_node11 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,17] 6 224 profile7_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,17] 6 224 profile7_node11_cert).mp (by decide +kernel))

def profile7_node12_cert : CutBound 8 := { lost := (rows 16 32 16 33 0 0 0 0), upper := (rows 225 19 37 216 208 32 64 128), lower := (rows 225 19 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 255 2 255 8 0 255 255 255), good := (rows 229 231 229 237 229 229 229 229) },{ target := 5, region := (rows 1 7 4 255 255 0 255 255), good := (rows 219 219 223 216 216 216 216 216) }] }

theorem profile7_node12 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,33] 6 208 profile7_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,33] 6 208 profile7_node12_cert).mp (by decide +kernel))

def profile7_node13_cert : CutBound 8 := { lost := (rows 16 32 1 48 0 0 0 0), upper := (rows 225 19 52 201 209 32 64 128), lower := (rows 225 19 52 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 255 255 255), good := (rows 224 246 244 232 244 224 224 224) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 212 200 208 192 192 192) }] }

theorem profile7_node13 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,48] 6 193 profile7_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,48] 6 193 profile7_node13_cert).mp (by decide +kernel))

def profile7_node14_cert : CutBound 8 := { lost := (rows 16 32 17 32 0 0 0 0), upper := (rows 225 19 100 153 145 32 64 128), lower := (rows 225 19 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 228 246 228 236 244 228 228 228) },{ target := 4, region := (rows 255 2 255 8 0 255 255 255), good := (rows 229 231 229 237 229 229 229 229) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 196 200 208 192 192 192) }] }

theorem profile7_node14 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,96] 6 145 profile7_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17,96] 6 145 profile7_node14_cert).mp (by decide +kernel))

def profile7_node10_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile7_node10_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile7_node10 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,17] 6 (by decide) (choices 2) [17,33,48,96] profile7_node10_route profile7_node10_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node11
  · exact profile7_node12
  · exact profile7_node13
  · exact profile7_node14

def profile7_node15_cert : CutBound 8 := { lost := (rows 16 16 32 32 0 0 0 0), upper := (rows 225 35 213 217 209 32 64 128), lower := (rows 225 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) },{ target := 5, region := (rows 1 2 7 11 19 0 255 255), good := (rows 221 223 196 200 208 192 192 192) }] }

theorem profile7_node15 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,33] 6 209 profile7_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,33] 6 209 profile7_node15_cert).mp (by decide +kernel))

def profile7_node16_cert : CutBound 8 := { lost := (rows 16 1 32 32 0 0 0 0), upper := (rows 225 50 213 217 209 32 64 128), lower := (rows 225 50 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 255 255 255), good := (rows 224 242 228 232 242 224 224 224) },{ target := 4, region := (rows 255 2 4 8 0 255 255 255), good := (rows 225 227 229 233 225 225 225 225) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 210 196 200 208 192 192 192) }] }

theorem profile7_node16 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,48] 6 209 profile7_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,48] 6 209 profile7_node16_cert).mp (by decide +kernel))

def profile7_node17_cert : CutBound 8 := { lost := (rows 16 17 32 32 0 0 0 0), upper := (rows 225 98 149 153 145 32 64 128), lower := (rows 225 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 194 196 200 208 192 192 192) }] }

theorem profile7_node17 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,96] 6 145 profile7_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224,96] 6 145 profile7_node17_cert).mp (by decide +kernel))

def profile7_node9_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile7_node9_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile7_node9 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [224] 6 (by decide) (choices 2) [17,33,48,96] profile7_node9_route profile7_node9_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node10
  · exact profile7_node15
  · exact profile7_node16
  · exact profile7_node17

def profile7_node0_column : Nat → Fin 8 := fun mask => match mask with | 14 => 1 | 22 => 1 | 38 => 1 | 70 => 1 | 134 => 1 | 26 => 1 | 42 => 1 | 74 => 1 | 138 => 1 | 50 => 1 | 82 => 1 | 146 => 1 | 98 => 1 | 162 => 1 | 194 => 1 | 28 => 2 | 44 => 2 | 76 => 2 | 140 => 2 | 52 => 2 | 84 => 2 | 148 => 2 | 100 => 2 | 164 => 2 | 196 => 2 | 56 => 3 | 88 => 3 | 152 => 3 | 104 => 3 | 168 => 3 | 200 => 3 | _ => 0

def profile7_node0_route : Route 8 := (fun mask => match mask with | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile7_node0 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [] 6 (by decide) (choices 3) [112,224] profile7_node0_route profile7_node0_column
    (by change RowCover 8 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile7_node1
  · exact profile7_node9

theorem profile7 : Upper (D (n:=8) [50,32,32,32,18,2,2,2]) (R (n:=8) [50,32,32,32,18,2,2,2]) [] 6 := profile7_node0


#print axioms profile7
end Delivery.SmallBudgetTenFinite8
