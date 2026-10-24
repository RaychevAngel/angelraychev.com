import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile23_node2_cert : CutBound 8 := { lost := (rows 0 224 16 16 0 0 0 0), upper := (rows 49 19 229 233 241 225 64 128), lower := (rows 49 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 255 255), good := (rows 237 239 196 200 192 224 192 192) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 211 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 179 147 132 136 144 160 128 128) },{ target := 7, region := (rows 1 3 4 8 16 32 255 0), good := (rows 115 83 68 72 80 96 64 64) }] }

theorem profile23_node2 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,17] 6 225 profile23_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,17] 6 225 profile23_node2_cert).mp (by decide +kernel))

def profile23_node3_cert : CutBound 8 := { lost := (rows 0 1 48 48 0 0 0 0), upper := (rows 49 50 197 201 209 225 64 128), lower := (rows 49 50 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 255 255), good := (rows 242 242 196 200 208 224 192 192) },{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 237 226 196 200 192 224 192 192) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 210 196 200 208 192 192 192) }] }

theorem profile23_node3 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,48] 6 193 profile23_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,48] 6 193 profile23_node3_cert).mp (by decide +kernel))

def profile23_node5_cert : CutBound 8 := { lost := (rows 0 48 32 17 0 0 0 0), upper := (rows 49 67 21 232 240 224 64 128), lower := (rows 49 67 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 7 4 255 0 255 255 255), good := (rows 235 235 239 232 232 232 232 232) },{ target := 5, region := (rows 1 7 5 8 16 0 255 255), good := (rows 215 199 215 200 208 192 192 192) }] }

theorem profile23_node5 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,17] 6 224 profile23_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,17] 6 224 profile23_node5_cert).mp (by decide +kernel))

def profile23_node6_cert : CutBound 8 := { lost := (rows 0 48 1 48 0 0 0 0), upper := (rows 49 67 52 201 209 225 64 128), lower := (rows 49 67 52 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 255 255), good := (rows 244 198 244 200 208 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 228 200 192 224 192 192) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 212 200 208 192 192 192) }] }

theorem profile23_node6 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,48] 6 193 profile23_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,48] 6 193 profile23_node6_cert).mp (by decide +kernel))

def profile23_node7_cert : CutBound 8 := { lost := (rows 0 48 48 1 0 0 0 0), upper := (rows 49 67 69 184 176 176 64 128), lower := (rows 49 67 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 7 7 8 0 32 255 255), good := (rows 231 199 199 200 192 224 192 192) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 215 199 199 200 208 192 192 192) }] }

theorem profile23_node7 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,65] 6 176 profile23_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,65] 6 176 profile23_node7_cert).mp (by decide +kernel))

def profile23_node8_cert : CutBound 8 := { lost := (rows 0 48 33 16 0 0 0 0), upper := (rows 49 67 84 169 177 161 64 128), lower := (rows 49 67 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 244 198 212 200 212 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) },{ target := 5, region := (rows 1 3 21 8 16 0 255 255), good := (rows 215 199 212 200 212 192 192 192) }] }

theorem profile23_node8 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,80] 6 161 profile23_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,80] 6 161 profile23_node8_cert).mp (by decide +kernel))

def profile23_node9_cert : CutBound 8 := { lost := (rows 0 48 48 1 0 0 0 0), upper := (rows 49 67 133 248 240 240 64 128), lower := (rows 49 67 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 7 7 8 0 32 255 255), good := (rows 231 199 199 200 192 224 192 192) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 215 199 199 200 208 192 192 192) }] }

theorem profile23_node9 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,129] 6 240 profile23_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,129] 6 240 profile23_node9_cert).mp (by decide +kernel))

def profile23_node10_cert : CutBound 8 := { lost := (rows 0 48 33 16 0 0 0 0), upper := (rows 49 67 148 233 241 225 64 128), lower := (rows 49 67 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 244 198 212 200 212 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) },{ target := 5, region := (rows 1 3 21 8 16 0 255 255), good := (rows 215 199 212 200 212 192 192 192) }] }

theorem profile23_node10 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,144] 6 225 profile23_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,144] 6 225 profile23_node10_cert).mp (by decide +kernel))

def profile23_node11_cert : CutBound 8 := { lost := (rows 0 48 49 0 0 0 0 0), upper := (rows 49 67 196 185 177 177 64 128), lower := (rows 49 67 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 244 198 196 204 212 228 196 196) },{ target := 4, region := (rows 1 3 255 8 0 32 255 255), good := (rows 231 199 196 204 196 228 196 196) },{ target := 5, region := (rows 1 3 255 8 16 0 255 255), good := (rows 215 199 196 204 212 196 196 196) }] }

theorem profile23_node11 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,192] 6 177 profile23_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65,192] 6 177 profile23_node11_cert).mp (by decide +kernel))

def profile23_node4_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile23_node4_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile23_node4 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,65] 6 (by decide) (choices 2) [17,48,65,80,129,144,192] profile23_node4_route profile23_node4_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node5
  · exact profile23_node6
  · exact profile23_node7
  · exact profile23_node8
  · exact profile23_node9
  · exact profile23_node10
  · exact profile23_node11

def profile23_node12_cert : CutBound 8 := { lost := (rows 0 161 16 16 0 0 0 0), upper := (rows 49 82 229 233 241 225 64 128), lower := (rows 49 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 242 210 196 200 210 224 192 192) },{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 237 194 196 200 192 224 192 192) },{ target := 5, region := (rows 1 19 4 8 16 0 255 255), good := (rows 211 210 196 200 210 192 192 192) },{ target := 7, region := (rows 1 19 4 8 16 32 255 0), good := (rows 115 82 68 72 82 96 64 64) }] }

theorem profile23_node12 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,80] 6 225 profile23_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,80] 6 225 profile23_node12_cert).mp (by decide +kernel))

def profile23_node14_cert : CutBound 8 := { lost := (rows 0 49 32 16 0 0 0 0), upper := (rows 49 194 21 233 241 225 64 128), lower := (rows 49 194 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 242 194 214 202 210 226 194 194) },{ target := 4, region := (rows 1 255 4 13 0 37 255 255), good := (rows 235 194 239 202 194 226 194 194) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 215 194 215 202 210 194 194 194) }] }

theorem profile23_node14 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,17] 6 225 profile23_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,17] 6 225 profile23_node14_cert).mp (by decide +kernel))

def profile23_node15_cert : CutBound 8 := { lost := (rows 0 49 1 48 0 0 0 0), upper := (rows 49 194 52 201 209 225 64 128), lower := (rows 49 194 52 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 5 8 16 32 255 255), good := (rows 246 194 246 202 210 226 194 194) },{ target := 4, region := (rows 1 255 4 9 0 33 255 255), good := (rows 235 194 230 202 194 226 194 194) },{ target := 5, region := (rows 1 255 4 9 17 0 255 255), good := (rows 219 194 214 202 210 194 194 194) }] }

theorem profile23_node15 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,48] 6 193 profile23_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,48] 6 193 profile23_node15_cert).mp (by decide +kernel))

def profile23_node16_cert : CutBound 8 := { lost := (rows 0 49 48 0 0 0 0 0), upper := (rows 49 194 69 185 177 177 64 128), lower := (rows 49 194 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 242 194 198 202 210 226 194 194) },{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 231 194 199 202 194 226 194 194) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 215 194 199 202 210 194 194 194) }] }

theorem profile23_node16 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,65] 6 177 profile23_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,65] 6 177 profile23_node16_cert).mp (by decide +kernel))

def profile23_node17_cert : CutBound 8 := { lost := (rows 0 49 33 16 0 0 0 0), upper := (rows 49 194 84 169 177 161 64 128), lower := (rows 49 194 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 21 8 16 32 255 255), good := (rows 246 194 214 202 214 226 194 194) },{ target := 4, region := (rows 1 255 4 9 0 33 255 255), good := (rows 235 194 198 202 194 226 194 194) },{ target := 5, region := (rows 1 255 21 8 16 0 255 255), good := (rows 215 194 214 202 214 194 194 194) }] }

theorem profile23_node17 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,80] 6 161 profile23_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,80] 6 161 profile23_node17_cert).mp (by decide +kernel))

def profile23_node18_cert : CutBound 8 := { lost := (rows 0 49 49 0 0 0 0 0), upper := (rows 49 194 196 57 49 49 64 128), lower := (rows 49 194 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 32 255 255), good := (rows 246 198 198 206 214 230 198 198) },{ target := 4, region := (rows 1 255 255 8 0 32 255 255), good := (rows 231 198 198 206 198 230 198 198) },{ target := 5, region := (rows 1 255 255 8 16 0 255 255), good := (rows 215 198 198 206 214 198 198 198) }] }

theorem profile23_node18 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,192] 6 49 profile23_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192,192] 6 49 profile23_node18_cert).mp (by decide +kernel))

def profile23_node13_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile23_node13_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile23_node13 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48,192] 6 (by decide) (choices 2) [17,48,65,80,192] profile23_node13_route profile23_node13_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile23_node14
  · exact profile23_node15
  · exact profile23_node16
  · exact profile23_node17
  · exact profile23_node18

def profile23_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile23_node1_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile23_node1 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [48] 6 (by decide) (choices 2) [17,48,65,80,192] profile23_node1_route profile23_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile23_node2
  · exact profile23_node3
  · exact profile23_node4
  · exact profile23_node12
  · exact profile23_node13

def profile23_node20_cert : CutBound 8 := { lost := (rows 32 96 16 16 0 0 0 0), upper := (rows 81 19 229 233 241 225 64 128), lower := (rows 81 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 255 255), good := (rows 237 239 196 200 192 224 192 192) },{ target := 5, region := (rows 19 19 4 8 16 0 255 255), good := (rows 211 211 196 200 211 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 147 147 132 136 144 160 128 128) }] }

theorem profile23_node20 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,17] 6 225 profile23_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,17] 6 225 profile23_node20_cert).mp (by decide +kernel))

def profile23_node22_cert : CutBound 8 := { lost := (rows 32 16 32 17 0 0 0 0), upper := (rows 81 35 21 232 240 224 64 128), lower := (rows 81 35 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 7 4 255 0 255 255 255), good := (rows 235 235 239 232 232 232 232 232) },{ target := 5, region := (rows 21 2 21 8 16 0 255 255), good := (rows 213 199 213 200 213 192 192 192) }] }

theorem profile23_node22 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,17] 6 224 profile23_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,17] 6 224 profile23_node22_cert).mp (by decide +kernel))

def profile23_node23_cert : CutBound 8 := { lost := (rows 32 16 16 33 0 0 0 0), upper := (rows 81 35 37 216 208 240 64 128), lower := (rows 81 35 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 6 6 8 0 32 255 255), good := (rows 193 231 231 200 192 224 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile23_node23 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,33] 6 208 profile23_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,33] 6 208 profile23_node23_cert).mp (by decide +kernel))

def profile23_node24_cert : CutBound 8 := { lost := (rows 160 144 0 48 0 0 0 0), upper := (rows 81 35 52 201 209 225 64 128), lower := (rows 81 35 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 228 200 192 224 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) },{ target := 7, region := (rows 21 6 4 8 16 32 255 0), good := (rows 81 99 119 72 81 96 64 64) }] }

theorem profile23_node24 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,48] 6 193 profile23_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,48] 6 193 profile23_node24_cert).mp (by decide +kernel))

def profile23_node25_cert : CutBound 8 := { lost := (rows 32 64 48 65 0 0 0 0), upper := (rows 81 35 69 184 176 176 64 128), lower := (rows 81 35 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 2 7 8 0 32 255 255), good := (rows 197 231 197 200 192 224 192 192) },{ target := 5, region := (rows 17 2 23 8 16 0 255 255), good := (rows 213 199 197 200 213 192 192 192) },{ target := 6, region := (rows 1 7 4 255 255 255 0 255), good := (rows 187 187 191 184 184 184 184 184) }] }

theorem profile23_node25 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,65] 6 176 profile23_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,65] 6 176 profile23_node25_cert).mp (by decide +kernel))

def profile23_node26_cert : CutBound 8 := { lost := (rows 32 16 33 16 0 0 0 0), upper := (rows 81 35 84 169 177 161 64 128), lower := (rows 81 35 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 212 230 212 200 212 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) },{ target := 5, region := (rows 21 2 21 8 16 0 255 255), good := (rows 213 199 213 200 213 192 192 192) }] }

theorem profile23_node26 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,80] 6 161 profile23_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,80] 6 161 profile23_node26_cert).mp (by decide +kernel))

def profile23_node27_cert : CutBound 8 := { lost := (rows 32 64 17 96 0 0 0 0), upper := (rows 81 35 100 153 145 177 64 128), lower := (rows 81 35 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 255 255), good := (rows 208 230 228 200 208 228 192 192) },{ target := 4, region := (rows 1 2 38 8 0 32 255 255), good := (rows 193 231 228 200 192 228 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) },{ target := 6, region := (rows 1 3 4 11 19 35 0 255), good := (rows 187 187 164 136 144 160 128 128) }] }

theorem profile23_node27 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,96] 6 145 profile23_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,96] 6 145 profile23_node27_cert).mp (by decide +kernel))

def profile23_node28_cert : CutBound 8 := { lost := (rows 32 0 112 1 0 0 0 0), upper := (rows 81 35 133 248 240 240 64 128), lower := (rows 81 35 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 2 7 8 0 32 255 255), good := (rows 197 231 197 200 192 224 192 192) },{ target := 5, region := (rows 17 2 23 8 16 0 255 255), good := (rows 213 199 197 200 213 192 192 192) },{ target := 6, region := (rows 1 2 7 8 16 32 0 255), good := (rows 149 167 133 136 144 160 128 128) }] }

theorem profile23_node28 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,129] 6 240 profile23_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,129] 6 240 profile23_node28_cert).mp (by decide +kernel))

def profile23_node29_cert : CutBound 8 := { lost := (rows 32 16 33 16 0 0 0 0), upper := (rows 81 35 148 233 241 225 64 128), lower := (rows 81 35 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 212 230 212 200 212 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) },{ target := 5, region := (rows 21 2 21 8 16 0 255 255), good := (rows 213 199 213 200 213 192 192 192) }] }

theorem profile23_node29 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,144] 6 225 profile23_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,144] 6 225 profile23_node29_cert).mp (by decide +kernel))

def profile23_node30_cert : CutBound 8 := { lost := (rows 32 0 81 32 0 0 0 0), upper := (rows 81 35 164 217 209 241 64 128), lower := (rows 81 35 164 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 255 255), good := (rows 208 230 228 200 208 228 192 192) },{ target := 4, region := (rows 1 2 38 8 0 32 255 255), good := (rows 193 231 228 200 192 228 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) },{ target := 6, region := (rows 1 2 38 8 16 32 0 255), good := (rows 145 167 164 136 144 164 128 128) }] }

theorem profile23_node30 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,160] 6 209 profile23_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,160] 6 209 profile23_node30_cert).mp (by decide +kernel))

def profile23_node31_cert : CutBound 8 := { lost := (rows 32 64 49 64 0 0 0 0), upper := (rows 81 35 196 185 177 177 64 128), lower := (rows 81 35 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 212 230 196 204 212 228 196 196) },{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 231 196 204 196 228 196 196) },{ target := 5, region := (rows 17 2 255 8 16 0 255 255), good := (rows 213 199 196 204 213 196 196 196) },{ target := 6, region := (rows 1 3 4 11 19 35 0 255), good := (rows 187 187 132 136 144 160 128 128) }] }

theorem profile23_node31 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,192] 6 177 profile23_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33,192] 6 177 profile23_node31_cert).mp (by decide +kernel))

def profile23_node21_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile23_node21_route : Route 8 := (fun mask => (mask,id))

theorem profile23_node21 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,33] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile23_node21_route profile23_node21_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node22
  · exact profile23_node23
  · exact profile23_node24
  · exact profile23_node25
  · exact profile23_node26
  · exact profile23_node27
  · exact profile23_node28
  · exact profile23_node29
  · exact profile23_node30
  · exact profile23_node31

def profile23_node33_cert : CutBound 8 := { lost := (rows 160 0 144 48 0 0 0 0), upper := (rows 81 50 37 201 209 225 64 128), lower := (rows 81 50 37 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 13 0 37 255 255), good := (rows 237 226 237 200 192 224 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) },{ target := 7, region := (rows 19 2 6 8 16 32 255 0), good := (rows 81 119 101 72 81 96 64 64) }] }

theorem profile23_node33 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,33] 6 193 profile23_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,33] 6 193 profile23_node33_cert).mp (by decide +kernel))

def profile23_node34_cert : CutBound 8 := { lost := (rows 32 64 48 80 0 0 0 0), upper := (rows 81 50 69 169 177 161 64 128), lower := (rows 81 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 13 0 37 255 255), good := (rows 237 226 237 200 192 224 192 192) },{ target := 5, region := (rows 19 2 23 8 16 0 255 255), good := (rows 213 215 197 200 213 192 192 192) },{ target := 6, region := (rows 1 7 4 13 21 37 0 255), good := (rows 187 178 191 136 144 160 128 128) }] }

theorem profile23_node34 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,65] 6 161 profile23_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,65] 6 161 profile23_node34_cert).mp (by decide +kernel))

def profile23_node35_cert : CutBound 8 := { lost := (rows 32 0 17 48 0 0 0 0), upper := (rows 81 50 100 137 145 161 64 128), lower := (rows 81 50 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 255 255), good := (rows 208 246 228 200 208 228 192 192) },{ target := 4, region := (rows 1 2 39 9 0 33 255 255), good := (rows 237 230 228 200 192 228 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile23_node35 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,96] 6 129 profile23_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,96] 6 129 profile23_node35_cert).mp (by decide +kernel))

def profile23_node36_cert : CutBound 8 := { lost := (rows 32 0 112 16 0 0 0 0), upper := (rows 81 50 133 233 241 225 64 128), lower := (rows 81 50 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 13 0 37 255 255), good := (rows 237 226 237 200 192 224 192 192) },{ target := 5, region := (rows 19 2 23 8 16 0 255 255), good := (rows 213 215 197 200 213 192 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 149 178 133 136 144 160 128 128) }] }

theorem profile23_node36 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,129] 6 225 profile23_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,129] 6 225 profile23_node36_cert).mp (by decide +kernel))

def profile23_node37_cert : CutBound 8 := { lost := (rows 32 0 17 48 0 0 0 0), upper := (rows 81 50 164 201 209 225 64 128), lower := (rows 81 50 164 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 255 255), good := (rows 208 246 228 200 208 228 192 192) },{ target := 4, region := (rows 1 2 39 9 0 33 255 255), good := (rows 237 230 228 200 192 228 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile23_node37 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,160] 6 193 profile23_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,160] 6 193 profile23_node37_cert).mp (by decide +kernel))

def profile23_node38_cert : CutBound 8 := { lost := (rows 32 0 49 16 0 0 0 0), upper := (rows 81 50 196 169 177 161 64 128), lower := (rows 81 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 212 246 196 204 212 228 196 196) },{ target := 4, region := (rows 1 2 255 9 0 33 255 255), good := (rows 237 230 196 204 196 228 196 196) },{ target := 5, region := (rows 19 2 255 8 16 0 255 255), good := (rows 213 215 196 204 213 196 196 196) }] }

theorem profile23_node38 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,192] 6 161 profile23_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48,192] 6 161 profile23_node38_cert).mp (by decide +kernel))

def profile23_node32_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile23_node32_route : Route 8 := (fun mask => (mask,id))

theorem profile23_node32 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,48] 6 (by decide) (choices 2) [33,65,96,129,160,192] profile23_node32_route profile23_node32_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node33
  · exact profile23_node34
  · exact profile23_node35
  · exact profile23_node36
  · exact profile23_node37
  · exact profile23_node38

def profile23_node39_cert : CutBound 8 := { lost := (rows 32 48 64 64 0 0 0 0), upper := (rows 81 67 181 185 177 177 64 128), lower := (rows 81 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 5, region := (rows 17 19 4 8 16 0 255 255), good := (rows 211 195 196 200 211 192 192 192) },{ target := 6, region := (rows 1 2 7 11 19 35 0 255), good := (rows 189 191 132 136 144 160 128 128) }] }

theorem profile23_node39 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,65] 6 177 profile23_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,65] 6 177 profile23_node39_cert).mp (by decide +kernel))

def profile23_node40_cert : CutBound 8 := { lost := (rows 32 33 16 16 0 0 0 0), upper := (rows 81 82 165 169 177 161 64 128), lower := (rows 81 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 210 210 196 200 210 224 192 192) },{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 237 194 196 200 192 224 192 192) },{ target := 5, region := (rows 19 19 4 8 16 0 255 255), good := (rows 211 211 196 200 211 192 192 192) }] }

theorem profile23_node40 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,80] 6 161 profile23_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,80] 6 161 profile23_node40_cert).mp (by decide +kernel))

def profile23_node41_cert : CutBound 8 := { lost := (rows 32 17 64 64 0 0 0 0), upper := (rows 81 98 181 185 177 177 64 128), lower := (rows 81 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 208 226 196 200 208 226 192 192) },{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) },{ target := 5, region := (rows 17 2 4 8 16 0 255 255), good := (rows 209 194 196 200 209 192 192 192) },{ target := 6, region := (rows 1 2 5 9 17 33 0 255), good := (rows 189 162 132 136 144 160 128 128) }] }

theorem profile23_node41 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,96] 6 177 profile23_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,96] 6 177 profile23_node41_cert).mp (by decide +kernel))

def profile23_node42_cert : CutBound 8 := { lost := (rows 160 112 0 0 0 0 0 0), upper := (rows 81 131 245 249 241 241 64 128), lower := (rows 81 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 5, region := (rows 17 19 4 8 16 0 255 255), good := (rows 211 195 196 200 211 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 147 131 132 136 144 160 128 128) },{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 67 68 72 81 96 64 64) }] }

theorem profile23_node42 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,129] 6 241 profile23_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,129] 6 241 profile23_node42_cert).mp (by decide +kernel))

def profile23_node43_cert : CutBound 8 := { lost := (rows 32 33 16 16 0 0 0 0), upper := (rows 81 146 229 233 241 225 64 128), lower := (rows 81 146 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 210 210 196 200 210 224 192 192) },{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 237 194 196 200 192 224 192 192) },{ target := 5, region := (rows 19 19 4 8 16 0 255 255), good := (rows 211 211 196 200 211 192 192 192) }] }

theorem profile23_node43 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,144] 6 225 profile23_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,144] 6 225 profile23_node43_cert).mp (by decide +kernel))

def profile23_node44_cert : CutBound 8 := { lost := (rows 160 81 0 0 0 0 0 0), upper := (rows 81 162 245 249 241 241 64 128), lower := (rows 81 162 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 208 226 196 200 208 226 192 192) },{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) },{ target := 5, region := (rows 17 2 4 8 16 0 255 255), good := (rows 209 194 196 200 209 192 192 192) },{ target := 6, region := (rows 1 34 4 8 16 32 0 255), good := (rows 145 162 132 136 144 162 128 128) },{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 98 68 72 81 96 64 64) }] }

theorem profile23_node44 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,160] 6 241 profile23_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,160] 6 241 profile23_node44_cert).mp (by decide +kernel))

def profile23_node45_cert : CutBound 8 := { lost := (rows 32 49 64 64 0 0 0 0), upper := (rows 81 194 181 185 177 177 64 128), lower := (rows 81 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 210 194 198 202 210 226 194 194) },{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 195 194 198 202 194 226 194 194) },{ target := 5, region := (rows 17 255 4 8 16 0 255 255), good := (rows 211 194 198 202 211 194 194 194) },{ target := 6, region := (rows 1 2 5 9 17 33 0 255), good := (rows 189 130 132 136 144 160 128 128) }] }

theorem profile23_node45 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,192] 6 177 profile23_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80,192] 6 177 profile23_node45_cert).mp (by decide +kernel))

def profile23_node19_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile23_node19_route : Route 8 := (fun mask => (mask,id))

theorem profile23_node19 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [80] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile23_node19_route profile23_node19_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node20
  · exact profile23_node21
  · exact profile23_node32
  · exact profile23_node39
  · exact profile23_node40
  · exact profile23_node41
  · exact profile23_node42
  · exact profile23_node43
  · exact profile23_node44
  · exact profile23_node45

def profile23_node48_cert : CutBound 8 := { lost := (rows 48 32 32 17 0 0 0 0), upper := (rows 193 19 21 232 240 224 64 128), lower := (rows 193 19 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 22 22 8 16 0 255 255), good := (rows 193 215 215 201 215 193 193 193) }] }

theorem profile23_node48 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,17] 6 224 profile23_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,17] 6 224 profile23_node48_cert).mp (by decide +kernel))

def profile23_node49_cert : CutBound 8 := { lost := (rows 48 32 16 1 0 0 0 0), upper := (rows 193 19 37 248 240 240 64 128), lower := (rows 193 19 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 195 229 201 193 229 193 193) },{ target := 5, region := (rows 255 18 4 8 16 0 255 255), good := (rows 193 211 197 201 211 193 193 193) }] }

theorem profile23_node49 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,33] 6 240 profile23_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,33] 6 240 profile23_node49_cert).mp (by decide +kernel))

def profile23_node51_cert : CutBound 8 := { lost := (rows 48 32 1 16 0 0 0 0), upper := (rows 193 19 52 41 208 224 64 128), lower := (rows 193 19 52 41 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 255 255 255 255), good := (rows 244 246 244 252 244 244 244 244) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 255 4 8 255 0 255 255), good := (rows 211 211 215 219 211 211 211 211) }] }

theorem profile23_node51 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,33] 6 192 profile23_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,33] 6 192 profile23_node51_cert).mp (by decide +kernel))

def profile23_node52_cert : CutBound 8 := { lost := (rows 48 32 1 48 0 0 0 0), upper := (rows 193 19 52 73 176 160 64 128), lower := (rows 193 19 52 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 255 255 255 255), good := (rows 244 246 244 252 244 244 244 244) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 22 4 255 16 0 255 255), good := (rows 201 219 223 201 219 201 201 201) }] }

theorem profile23_node52 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,65] 6 160 profile23_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,65] 6 160 profile23_node52_cert).mp (by decide +kernel))

def profile23_node53_cert : CutBound 8 := { lost := (rows 48 32 0 17 0 0 0 0), upper := (rows 193 19 52 104 145 161 64 128), lower := (rows 193 19 52 104 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 44 16 32 255 255), good := (rows 192 210 252 232 208 232 192 192) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 255 4 8 255 0 255 255), good := (rows 211 211 215 219 211 211 211 211) }] }

theorem profile23_node53 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,96] 6 129 profile23_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,96] 6 129 profile23_node53_cert).mp (by decide +kernel))

def profile23_node54_cert : CutBound 8 := { lost := (rows 48 32 0 49 0 0 0 0), upper := (rows 193 19 52 200 49 33 64 128), lower := (rows 193 19 52 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 218 252 200 216 232 200 200) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 22 4 255 16 0 255 255), good := (rows 201 219 223 201 219 201 201 201) }] }

theorem profile23_node54 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,192] 6 33 profile23_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48,192] 6 33 profile23_node54_cert).mp (by decide +kernel))

def profile23_node50_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile23_node50_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile23_node50 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,48] 6 (by decide) (choices 2) [33,65,96,192] profile23_node50_route profile23_node50_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile23_node51
  · exact profile23_node52
  · exact profile23_node53
  · exact profile23_node54

def profile23_node55_cert : CutBound 8 := { lost := (rows 48 32 48 1 0 0 0 0), upper := (rows 193 19 69 184 176 176 64 128), lower := (rows 193 19 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) },{ target := 5, region := (rows 255 18 255 8 16 0 255 255), good := (rows 197 215 197 205 215 197 197 197) }] }

theorem profile23_node55 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,65] 6 176 profile23_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,65] 6 176 profile23_node55_cert).mp (by decide +kernel))

def profile23_node56_cert : CutBound 8 := { lost := (rows 48 32 33 16 0 0 0 0), upper := (rows 193 19 84 169 177 161 64 128), lower := (rows 193 19 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 192 214 212 200 212 224 192 192) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 22 22 8 16 0 255 255), good := (rows 193 215 215 201 215 193 193 193) }] }

theorem profile23_node56 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,80] 6 161 profile23_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,80] 6 161 profile23_node56_cert).mp (by decide +kernel))

def profile23_node57_cert : CutBound 8 := { lost := (rows 48 32 17 0 0 0 0 0), upper := (rows 193 19 100 185 177 177 64 128), lower := (rows 193 19 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 255 255), good := (rows 192 210 228 200 208 228 192 192) },{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 195 229 201 193 229 193 193) },{ target := 5, region := (rows 255 18 4 8 16 0 255 255), good := (rows 193 211 197 201 211 193 193 193) }] }

theorem profile23_node57 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,96] 6 177 profile23_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,96] 6 177 profile23_node57_cert).mp (by decide +kernel))

def profile23_node58_cert : CutBound 8 := { lost := (rows 48 32 49 0 0 0 0 0), upper := (rows 193 19 196 57 49 49 64 128), lower := (rows 193 19 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 214 196 204 212 228 196 196) },{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) },{ target := 5, region := (rows 255 18 255 8 16 0 255 255), good := (rows 197 215 197 205 215 197 197 197) }] }

theorem profile23_node58 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,192] 6 49 profile23_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17,192] 6 49 profile23_node58_cert).mp (by decide +kernel))

def profile23_node47_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile23_node47_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile23_node47 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,17] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile23_node47_route profile23_node47_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node48
  · exact profile23_node49
  · exact profile23_node50
  · exact profile23_node55
  · exact profile23_node56
  · exact profile23_node57
  · exact profile23_node58

def profile23_node61_cert : CutBound 8 := { lost := (rows 48 1 32 16 0 0 0 0), upper := (rows 193 50 21 41 208 224 64 128), lower := (rows 193 50 21 41 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 2 255 8 255 0 255 255), good := (rows 213 215 213 221 213 213 213 213) }] }

theorem profile23_node61 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,33] 6 192 profile23_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,33] 6 192 profile23_node61_cert).mp (by decide +kernel))

def profile23_node62_cert : CutBound 8 := { lost := (rows 48 1 32 48 0 0 0 0), upper := (rows 193 50 21 73 176 160 64 128), lower := (rows 193 50 21 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 2 22 255 16 0 255 255), good := (rows 201 223 221 201 221 201 201 201) }] }

theorem profile23_node62 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,65] 6 160 profile23_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,65] 6 160 profile23_node62_cert).mp (by decide +kernel))

def profile23_node63_cert : CutBound 8 := { lost := (rows 48 0 32 17 0 0 0 0), upper := (rows 193 50 21 104 145 161 64 128), lower := (rows 193 50 21 104 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 42 16 32 255 255), good := (rows 192 250 212 232 208 232 192 192) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 2 255 8 255 0 255 255), good := (rows 213 215 213 221 213 213 213 213) }] }

theorem profile23_node63 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,96] 6 129 profile23_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,96] 6 129 profile23_node63_cert).mp (by decide +kernel))

def profile23_node64_cert : CutBound 8 := { lost := (rows 48 0 32 49 0 0 0 0), upper := (rows 193 50 21 200 49 33 64 128), lower := (rows 193 50 21 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 250 220 200 216 232 200 200) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 2 22 255 16 0 255 255), good := (rows 201 223 221 201 221 201 201 201) }] }

theorem profile23_node64 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,192] 6 33 profile23_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17,192] 6 33 profile23_node64_cert).mp (by decide +kernel))

def profile23_node60_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile23_node60_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile23_node60 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,17] 6 (by decide) (choices 2) [33,65,96,192] profile23_node60_route profile23_node60_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile23_node61
  · exact profile23_node62
  · exact profile23_node63
  · exact profile23_node64

def profile23_node65_cert : CutBound 8 := { lost := (rows 48 1 1 48 0 0 0 0), upper := (rows 193 50 52 201 209 225 64 128), lower := (rows 193 50 52 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 6 8 16 32 255 255), good := (rows 192 246 246 200 208 224 192 192) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile23_node65 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,48] 6 193 profile23_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,48] 6 193 profile23_node65_cert).mp (by decide +kernel))

def profile23_node66_cert : CutBound 8 := { lost := (rows 48 64 48 64 0 0 0 0), upper := (rows 193 50 69 185 177 177 64 128), lower := (rows 193 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) },{ target := 5, region := (rows 255 2 255 8 16 0 255 255), good := (rows 197 215 197 205 213 197 197 197) },{ target := 6, region := (rows 1 7 4 13 21 37 0 255), good := (rows 187 178 191 136 144 160 128 128) }] }

theorem profile23_node66 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,65] 6 177 profile23_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,65] 6 177 profile23_node66_cert).mp (by decide +kernel))

def profile23_node67_cert : CutBound 8 := { lost := (rows 48 0 33 16 0 0 0 0), upper := (rows 193 50 84 169 177 161 64 128), lower := (rows 193 50 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 192 246 212 200 212 224 192 192) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 255 2 22 8 16 0 255 255), good := (rows 193 215 213 201 213 193 193 193) }] }

theorem profile23_node67 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,80] 6 161 profile23_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,80] 6 161 profile23_node67_cert).mp (by decide +kernel))

def profile23_node68_cert : CutBound 8 := { lost := (rows 48 0 49 0 0 0 0 0), upper := (rows 193 50 196 57 49 49 64 128), lower := (rows 193 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 246 196 204 212 228 196 196) },{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) },{ target := 5, region := (rows 255 2 255 8 16 0 255 255), good := (rows 197 215 197 205 213 197 197 197) }] }

theorem profile23_node68 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,192] 6 49 profile23_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48,192] 6 49 profile23_node68_cert).mp (by decide +kernel))

def profile23_node59_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile23_node59_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile23_node59 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,48] 6 (by decide) (choices 2) [17,48,65,80,192] profile23_node59_route profile23_node59_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile23_node60
  · exact profile23_node65
  · exact profile23_node66
  · exact profile23_node67
  · exact profile23_node68

def profile23_node69_cert : CutBound 8 := { lost := (rows 48 48 64 64 0 0 0 0), upper := (rows 193 67 181 185 177 177 64 128), lower := (rows 193 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 5, region := (rows 255 255 4 8 16 0 255 255), good := (rows 195 195 199 203 211 195 195 195) },{ target := 6, region := (rows 1 2 7 11 19 35 0 255), good := (rows 189 191 132 136 144 160 128 128) }] }

theorem profile23_node69 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,65] 6 177 profile23_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,65] 6 177 profile23_node69_cert).mp (by decide +kernel))

def profile23_node70_cert : CutBound 8 := { lost := (rows 48 33 64 64 0 0 0 0), upper := (rows 193 82 181 185 177 177 64 128), lower := (rows 193 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 192 210 196 200 210 224 192 192) },{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) },{ target := 5, region := (rows 255 18 4 8 16 0 255 255), good := (rows 193 211 197 201 211 193 193 193) },{ target := 6, region := (rows 1 2 5 9 17 33 0 255), good := (rows 189 146 132 136 144 160 128 128) }] }

theorem profile23_node70 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,80] 6 177 profile23_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,80] 6 177 profile23_node70_cert).mp (by decide +kernel))

def profile23_node71_cert : CutBound 8 := { lost := (rows 48 49 0 0 0 0 0 0), upper := (rows 193 194 53 57 49 49 64 128), lower := (rows 193 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 194 194 198 202 210 226 194 194) },{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 5, region := (rows 255 255 4 8 16 0 255 255), good := (rows 195 195 199 203 211 195 195 195) }] }

theorem profile23_node71 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,192] 6 49 profile23_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192,192] 6 49 profile23_node71_cert).mp (by decide +kernel))

def profile23_node46_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile23_node46_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile23_node46 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [192] 6 (by decide) (choices 2) [17,48,65,80,192] profile23_node46_route profile23_node46_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile23_node47
  · exact profile23_node59
  · exact profile23_node69
  · exact profile23_node70
  · exact profile23_node71

def profile23_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile23_node0_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile23_node0 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [] 6 (by decide) (choices 2) [48,80,192] profile23_node0_route profile23_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node1
  · exact profile23_node19
  · exact profile23_node46

theorem profile23 : Upper (D (n:=8) [34,32,32,32,18,18,2,2]) (R (n:=8) [34,32,32,32,18,18,2,2]) [] 6 := profile23_node0


#print axioms profile23
end Delivery.SmallBudgetTenFinite8
