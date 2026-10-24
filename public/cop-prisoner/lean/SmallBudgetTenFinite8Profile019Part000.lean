import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile19_node2_cert : CutBound 8 := { lost := (rows 64 64 16 16 0 0 0 0), upper := (rows 19 19 229 233 241 225 64 128), lower := (rows 19 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 255 255), good := (rows 239 239 196 200 192 224 192 192) },{ target := 6, region := (rows 19 19 4 8 16 32 0 255), good := (rows 147 147 132 136 147 160 128 128) }] }

theorem profile19_node2 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,17] 6 225 profile19_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,17] 6 225 profile19_node2_cert).mp (by decide +kernel))

def profile19_node4_cert : CutBound 8 := { lost := (rows 0 16 0 17 0 0 0 0), upper := (rows 19 35 21 200 208 224 64 128), lower := (rows 19 35 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 250 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 7 4 255 0 255 255 255), good := (rows 235 235 239 232 232 232 232 232) }] }

theorem profile19_node4 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,17] 6 192 profile19_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,17] 6 192 profile19_node4_cert).mp (by decide +kernel))

def profile19_node5_cert : CutBound 8 := { lost := (rows 0 0 144 1 0 0 0 0), upper := (rows 19 35 69 216 208 240 64 128), lower := (rows 19 35 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 250 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 2 7 8 0 32 255 255), good := (rows 199 231 197 200 192 224 192 192) },{ target := 7, region := (rows 1 2 7 8 16 32 255 0), good := (rows 87 103 69 72 80 96 64 64) }] }

theorem profile19_node5 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,65] 6 208 profile19_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,65] 6 208 profile19_node5_cert).mp (by decide +kernel))

def profile19_node6_cert : CutBound 8 := { lost := (rows 0 16 1 16 0 0 0 0), upper := (rows 19 35 84 201 209 225 64 128), lower := (rows 19 35 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 214 230 212 200 212 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile19_node6 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,80] 6 193 profile19_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,80] 6 193 profile19_node6_cert).mp (by decide +kernel))

def profile19_node8_cert : CutBound 8 := { lost := (rows 0 16 17 0 0 0 0 0), upper := (rows 19 35 196 25 208 224 64 128), lower := (rows 19 35 196 25 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 255 255 255 255), good := (rows 246 246 244 252 244 244 244 244) },{ target := 4, region := (rows 1 11 255 8 0 255 255 255), good := (rows 231 231 228 239 228 228 228 228) }] }

theorem profile19_node8 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,17] 6 192 profile19_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,17] 6 192 profile19_node8_cert).mp (by decide +kernel))

def profile19_node9_cert : CutBound 8 := { lost := (rows 0 0 17 16 0 0 0 0), upper := (rows 19 35 196 73 144 176 64 128), lower := (rows 19 35 196 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 255 255 255 255), good := (rows 246 246 244 252 244 244 244 244) },{ target := 4, region := (rows 1 2 255 11 0 32 255 255), good := (rows 207 239 196 205 196 228 196 196) }] }

theorem profile19_node9 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,65] 6 144 profile19_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,65] 6 144 profile19_node9_cert).mp (by decide +kernel))

def profile19_node10_cert : CutBound 8 := { lost := (rows 0 16 17 1 0 0 0 0), upper := (rows 19 35 196 88 145 161 64 128), lower := (rows 19 35 196 88 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 25 16 32 255 255), good := (rows 222 238 196 220 220 228 196 196) },{ target := 4, region := (rows 1 3 255 8 0 35 255 255), good := (rows 231 231 196 204 196 228 196 196) }] }

theorem profile19_node10 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,80] 6 129 profile19_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,80] 6 129 profile19_node10_cert).mp (by decide +kernel))

def profile19_node11_cert : CutBound 8 := { lost := (rows 0 0 17 17 0 0 0 0), upper := (rows 19 35 196 200 17 49 64 128), lower := (rows 19 35 196 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 255 16 32 255 255), good := (rows 222 238 204 204 220 236 204 204) },{ target := 4, region := (rows 1 2 255 255 0 32 255 255), good := (rows 207 239 204 204 204 236 204 204) }] }

theorem profile19_node11 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,192] 6 17 profile19_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192,192] 6 17 profile19_node11_cert).mp (by decide +kernel))

def profile19_node7_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node7_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node7 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33,192] 6 (by decide) (choices 2) [17,65,80,192] profile19_node7_route profile19_node7_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node8
  · exact profile19_node9
  · exact profile19_node10
  · exact profile19_node11

def profile19_node3_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node3_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node3 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,33] 6 (by decide) (choices 2) [17,65,80,192] profile19_node3_route profile19_node3_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node4
  · exact profile19_node5
  · exact profile19_node6
  · exact profile19_node7

def profile19_node12_cert : CutBound 8 := { lost := (rows 64 0 16 16 0 0 0 0), upper := (rows 19 50 197 201 209 225 64 128), lower := (rows 19 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 239 226 196 200 192 224 192 192) },{ target := 6, region := (rows 3 2 4 8 16 32 0 255), good := (rows 147 179 132 136 144 160 128 128) }] }

theorem profile19_node12 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,48] 6 193 profile19_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,48] 6 193 profile19_node12_cert).mp (by decide +kernel))

def profile19_node13_cert : CutBound 8 := { lost := (rows 128 144 0 0 0 0 0 0), upper := (rows 19 67 245 249 241 241 64 128), lower := (rows 19 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 7, region := (rows 17 19 4 8 16 32 255 0), good := (rows 83 67 68 72 83 96 64 64) }] }

theorem profile19_node13 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,65] 6 241 profile19_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,65] 6 241 profile19_node13_cert).mp (by decide +kernel))

def profile19_node14_cert : CutBound 8 := { lost := (rows 0 1 16 16 0 0 0 0), upper := (rows 19 82 229 233 241 225 64 128), lower := (rows 19 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 210 210 196 200 210 224 192 192) },{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 239 194 196 200 192 224 192 192) }] }

theorem profile19_node14 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,80] 6 225 profile19_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,80] 6 225 profile19_node14_cert).mp (by decide +kernel))

def profile19_node15_cert : CutBound 8 := { lost := (rows 0 145 0 0 0 0 0 0), upper := (rows 19 98 213 217 209 241 64 128), lower := (rows 19 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 210 226 196 200 208 226 192 192) },{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 195 226 196 200 192 226 192 192) },{ target := 7, region := (rows 1 34 4 8 16 32 255 0), good := (rows 83 98 68 72 80 98 64 64) }] }

theorem profile19_node15 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,96] 6 209 profile19_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,96] 6 209 profile19_node15_cert).mp (by decide +kernel))

def profile19_node17_cert : CutBound 8 := { lost := (rows 0 17 0 16 0 0 0 0), upper := (rows 19 194 21 233 241 225 64 128), lower := (rows 19 194 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 210 194 214 202 210 226 194 194) },{ target := 4, region := (rows 1 255 4 13 0 37 255 255), good := (rows 235 194 239 202 194 226 194 194) }] }

theorem profile19_node17 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,17] 6 225 profile19_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,17] 6 225 profile19_node17_cert).mp (by decide +kernel))

def profile19_node19_cert : CutBound 8 := { lost := (rows 0 17 16 0 0 0 0 0), upper := (rows 19 194 37 25 208 224 64 128), lower := (rows 19 194 37 25 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 4, region := (rows 1 255 13 8 0 255 255 255), good := (rows 231 226 231 239 226 226 226 226) }] }

theorem profile19_node19 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,17] 6 192 profile19_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,17] 6 192 profile19_node19_cert).mp (by decide +kernel))

def profile19_node20_cert : CutBound 8 := { lost := (rows 0 17 0 16 0 0 0 0), upper := (rows 19 194 37 73 144 176 64 128), lower := (rows 19 194 37 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 4, region := (rows 1 255 4 13 0 32 255 255), good := (rows 203 194 239 203 194 226 194 194) }] }

theorem profile19_node20 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,65] 6 144 profile19_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,65] 6 144 profile19_node20_cert).mp (by decide +kernel))

def profile19_node21_cert : CutBound 8 := { lost := (rows 0 17 16 1 0 0 0 0), upper := (rows 19 194 37 88 145 161 64 128), lower := (rows 19 194 37 88 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 25 16 32 255 255), good := (rows 218 194 238 218 218 226 194 194) },{ target := 4, region := (rows 1 255 5 8 0 37 255 255), good := (rows 231 194 231 202 194 226 194 194) }] }

theorem profile19_node21 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,80] 6 129 profile19_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,80] 6 129 profile19_node21_cert).mp (by decide +kernel))

def profile19_node22_cert : CutBound 8 := { lost := (rows 0 17 0 17 0 0 0 0), upper := (rows 19 194 37 200 17 49 64 128), lower := (rows 19 194 37 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 255 16 32 255 255), good := (rows 218 202 238 202 218 234 202 202) },{ target := 4, region := (rows 1 255 4 255 0 32 255 255), good := (rows 203 202 239 202 202 234 202 202) }] }

theorem profile19_node22 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,192] 6 17 profile19_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33,192] 6 17 profile19_node22_cert).mp (by decide +kernel))

def profile19_node18_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node18_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node18 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,33] 6 (by decide) (choices 2) [17,65,80,192] profile19_node18_route profile19_node18_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node19
  · exact profile19_node20
  · exact profile19_node21
  · exact profile19_node22

def profile19_node23_cert : CutBound 8 := { lost := (rows 0 17 0 16 0 0 0 0), upper := (rows 19 194 52 201 209 225 64 128), lower := (rows 19 194 52 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 210 194 246 202 210 226 194 194) },{ target := 4, region := (rows 1 255 4 9 0 33 255 255), good := (rows 235 194 230 202 194 226 194 194) }] }

theorem profile19_node23 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,48] 6 193 profile19_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,48] 6 193 profile19_node23_cert).mp (by decide +kernel))

def profile19_node24_cert : CutBound 8 := { lost := (rows 0 17 16 0 0 0 0 0), upper := (rows 19 194 69 185 177 177 64 128), lower := (rows 19 194 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 210 194 198 202 210 226 194 194) },{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 199 194 199 202 194 226 194 194) }] }

theorem profile19_node24 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,65] 6 177 profile19_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,65] 6 177 profile19_node24_cert).mp (by decide +kernel))

def profile19_node25_cert : CutBound 8 := { lost := (rows 0 17 1 16 0 0 0 0), upper := (rows 19 194 84 169 177 161 64 128), lower := (rows 19 194 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 21 8 16 32 255 255), good := (rows 214 194 214 202 214 226 194 194) },{ target := 4, region := (rows 1 255 4 9 0 33 255 255), good := (rows 235 194 198 202 194 226 194 194) }] }

theorem profile19_node25 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,80] 6 161 profile19_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,80] 6 161 profile19_node25_cert).mp (by decide +kernel))

def profile19_node26_cert : CutBound 8 := { lost := (rows 0 17 17 0 0 0 0 0), upper := (rows 19 194 100 153 145 177 64 128), lower := (rows 19 194 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 36 8 16 32 255 255), good := (rows 210 194 230 202 210 230 194 194) },{ target := 4, region := (rows 1 255 36 8 0 32 255 255), good := (rows 195 194 230 202 194 230 194 194) }] }

theorem profile19_node26 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,96] 6 145 profile19_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,96] 6 145 profile19_node26_cert).mp (by decide +kernel))

def profile19_node27_cert : CutBound 8 := { lost := (rows 0 17 17 0 0 0 0 0), upper := (rows 19 194 196 57 49 49 64 128), lower := (rows 19 194 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 32 255 255), good := (rows 214 198 198 206 214 230 198 198) },{ target := 4, region := (rows 1 255 255 8 0 32 255 255), good := (rows 199 198 198 206 198 230 198 198) }] }

theorem profile19_node27 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,192] 6 49 profile19_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192,192] 6 49 profile19_node27_cert).mp (by decide +kernel))

def profile19_node16_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile19_node16_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node16 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18,192] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile19_node16_route profile19_node16_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node17
  · exact profile19_node18
  · exact profile19_node23
  · exact profile19_node24
  · exact profile19_node25
  · exact profile19_node26
  · exact profile19_node27

def profile19_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile19_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node1 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [18] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile19_node1_route profile19_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node2
  · exact profile19_node3
  · exact profile19_node12
  · exact profile19_node13
  · exact profile19_node14
  · exact profile19_node15
  · exact profile19_node16

def profile19_node30_cert : CutBound 8 := { lost := (rows 16 0 0 17 0 0 0 0), upper := (rows 35 19 21 200 208 224 64 128), lower := (rows 35 19 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 250 250 252 248 248 248 248 248) },{ target := 4, region := (rows 3 2 4 255 0 255 255 255), good := (rows 235 235 237 232 232 232 232 232) }] }

theorem profile19_node30 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,17] 6 192 profile19_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,17] 6 192 profile19_node30_cert).mp (by decide +kernel))

def profile19_node31_cert : CutBound 8 := { lost := (rows 0 0 144 1 0 0 0 0), upper := (rows 35 19 69 216 208 240 64 128), lower := (rows 35 19 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 250 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 2 7 8 0 32 255 255), good := (rows 231 199 197 200 192 224 192 192) },{ target := 7, region := (rows 1 2 7 8 16 32 255 0), good := (rows 103 87 69 72 80 96 64 64) }] }

theorem profile19_node31 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,65] 6 208 profile19_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,65] 6 208 profile19_node31_cert).mp (by decide +kernel))

def profile19_node32_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 35 19 84 201 209 225 64 128), lower := (rows 35 19 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 230 214 212 200 212 224 192 192) },{ target := 4, region := (rows 3 2 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile19_node32 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,80] 6 193 profile19_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,80] 6 193 profile19_node32_cert).mp (by decide +kernel))

def profile19_node34_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 35 19 196 25 208 224 64 128), lower := (rows 35 19 196 25 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 255 255 255 255), good := (rows 246 246 244 252 244 244 244 244) },{ target := 4, region := (rows 3 2 255 8 0 255 255 255), good := (rows 231 231 228 237 228 228 228 228) }] }

theorem profile19_node34 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,17] 6 192 profile19_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,17] 6 192 profile19_node34_cert).mp (by decide +kernel))

def profile19_node35_cert : CutBound 8 := { lost := (rows 0 0 17 16 0 0 0 0), upper := (rows 35 19 196 73 144 176 64 128), lower := (rows 35 19 196 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 255 255 255 255), good := (rows 246 246 244 252 244 244 244 244) },{ target := 4, region := (rows 1 2 255 11 0 32 255 255), good := (rows 239 207 196 205 196 228 196 196) }] }

theorem profile19_node35 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,65] 6 144 profile19_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,65] 6 144 profile19_node35_cert).mp (by decide +kernel))

def profile19_node36_cert : CutBound 8 := { lost := (rows 16 0 17 1 0 0 0 0), upper := (rows 35 19 196 88 145 161 64 128), lower := (rows 35 19 196 88 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 26 16 32 255 255), good := (rows 238 222 196 220 220 228 196 196) },{ target := 4, region := (rows 3 2 255 8 0 35 255 255), good := (rows 231 231 196 204 196 228 196 196) }] }

theorem profile19_node36 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,80] 6 129 profile19_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,80] 6 129 profile19_node36_cert).mp (by decide +kernel))

def profile19_node37_cert : CutBound 8 := { lost := (rows 0 0 17 17 0 0 0 0), upper := (rows 35 19 196 200 17 49 64 128), lower := (rows 35 19 196 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 255 16 32 255 255), good := (rows 238 222 204 204 220 236 204 204) },{ target := 4, region := (rows 1 2 255 255 0 32 255 255), good := (rows 239 207 204 204 204 236 204 204) }] }

theorem profile19_node37 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,192] 6 17 profile19_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192,192] 6 17 profile19_node37_cert).mp (by decide +kernel))

def profile19_node33_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node33_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node33 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17,192] 6 (by decide) (choices 2) [17,65,80,192] profile19_node33_route profile19_node33_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node34
  · exact profile19_node35
  · exact profile19_node36
  · exact profile19_node37

def profile19_node29_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node29_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node29 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,17] 6 (by decide) (choices 2) [17,65,80,192] profile19_node29_route profile19_node29_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node30
  · exact profile19_node31
  · exact profile19_node32
  · exact profile19_node33

def profile19_node38_cert : CutBound 8 := { lost := (rows 144 144 0 0 0 0 0 0), upper := (rows 35 67 213 217 209 241 64 128), lower := (rows 35 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 255 255), good := (rows 227 195 196 200 192 227 192 192) },{ target := 7, region := (rows 33 35 4 8 16 32 255 0), good := (rows 99 67 68 72 80 99 64 64) }] }

theorem profile19_node38 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,65] 6 209 profile19_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,65] 6 209 profile19_node38_cert).mp (by decide +kernel))

def profile19_node40_cert : CutBound 8 := { lost := (rows 16 1 0 16 0 0 0 0), upper := (rows 35 82 21 201 209 225 64 128), lower := (rows 35 82 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 22 4 8 16 32 255 255), good := (rows 226 210 214 200 210 224 192 192) },{ target := 4, region := (rows 3 2 4 15 0 39 255 255), good := (rows 235 235 237 200 192 224 192 192) }] }

theorem profile19_node40 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,17] 6 193 profile19_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,17] 6 193 profile19_node40_cert).mp (by decide +kernel))

def profile19_node41_cert : CutBound 8 := { lost := (rows 64 1 16 64 0 0 0 0), upper := (rows 35 82 69 153 145 177 64 128), lower := (rows 35 82 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 226 210 196 200 210 224 192 192) },{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 231 194 197 200 192 224 192 192) },{ target := 6, region := (rows 3 2 4 15 23 39 0 255), good := (rows 187 187 189 136 144 160 128 128) }] }

theorem profile19_node41 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,65] 6 145 profile19_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,65] 6 145 profile19_node41_cert).mp (by decide +kernel))

def profile19_node42_cert : CutBound 8 := { lost := (rows 16 1 1 16 0 0 0 0), upper := (rows 35 82 84 137 145 161 64 128), lower := (rows 35 82 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 255 255), good := (rows 230 214 214 200 214 224 192 192) },{ target := 4, region := (rows 3 2 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile19_node42 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,80] 6 129 profile19_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,80] 6 129 profile19_node42_cert).mp (by decide +kernel))

def profile19_node43_cert : CutBound 8 := { lost := (rows 0 1 80 0 0 0 0 0), upper := (rows 35 82 133 217 209 241 64 128), lower := (rows 35 82 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 226 210 196 200 210 224 192 192) },{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 231 194 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 167 146 133 136 144 160 128 128) }] }

theorem profile19_node43 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,129] 6 209 profile19_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,129] 6 209 profile19_node43_cert).mp (by decide +kernel))

def profile19_node44_cert : CutBound 8 := { lost := (rows 16 1 1 16 0 0 0 0), upper := (rows 35 82 148 201 209 225 64 128), lower := (rows 35 82 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 255 255), good := (rows 230 214 214 200 214 224 192 192) },{ target := 4, region := (rows 3 2 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile19_node44 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,144] 6 193 profile19_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,144] 6 193 profile19_node44_cert).mp (by decide +kernel))

def profile19_node45_cert : CutBound 8 := { lost := (rows 0 1 17 0 0 0 0 0), upper := (rows 35 82 196 153 145 177 64 128), lower := (rows 35 82 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 255 8 16 32 255 255), good := (rows 230 214 196 204 214 228 196 196) },{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 231 198 196 204 196 228 196 196) }] }

theorem profile19_node45 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,192] 6 145 profile19_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80,192] 6 145 profile19_node45_cert).mp (by decide +kernel))

def profile19_node39_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node39_route : Route 8 := (fun mask => (mask,id))

theorem profile19_node39 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,80] 6 (by decide) (choices 2) [17,65,80,129,144,192] profile19_node39_route profile19_node39_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node40
  · exact profile19_node41
  · exact profile19_node42
  · exact profile19_node43
  · exact profile19_node44
  · exact profile19_node45

def profile19_node46_cert : CutBound 8 := { lost := (rows 16 17 0 0 0 0 0 0), upper := (rows 35 194 213 217 209 241 64 128), lower := (rows 35 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 226 194 198 202 210 226 194 194) },{ target := 4, region := (rows 33 255 4 8 0 32 255 255), good := (rows 227 194 198 202 194 227 194 194) }] }

theorem profile19_node46 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,192] 6 209 profile19_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34,192] 6 209 profile19_node46_cert).mp (by decide +kernel))

def profile19_node28_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node28_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node28 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [34] 6 (by decide) (choices 2) [17,65,80,192] profile19_node28_route profile19_node28_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node29
  · exact profile19_node38
  · exact profile19_node39
  · exact profile19_node46

def profile19_node48_cert : CutBound 8 := { lost := (rows 0 64 16 16 0 0 0 0), upper := (rows 49 19 199 203 211 227 64 128), lower := (rows 49 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 255 255), good := (rows 225 239 196 200 192 224 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 179 147 132 136 144 160 128 128) }] }

theorem profile19_node48 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,17] 6 195 profile19_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,17] 6 195 profile19_node48_cert).mp (by decide +kernel))

def profile19_node50_cert : CutBound 8 := { lost := (rows 0 16 16 1 0 0 0 0), upper := (rows 49 67 7 216 208 240 64 128), lower := (rows 49 67 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 254 248 248 248 248 248) },{ target := 4, region := (rows 1 7 7 8 0 32 255 255), good := (rows 231 199 199 200 192 224 192 192) }] }

theorem profile19_node50 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,3] 6 208 profile19_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,3] 6 208 profile19_node50_cert).mp (by decide +kernel))

def profile19_node51_cert : CutBound 8 := { lost := (rows 0 16 0 17 0 0 0 0), upper := (rows 49 67 21 202 210 226 64 128), lower := (rows 49 67 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 240 250 212 200 208 224 192 192) },{ target := 4, region := (rows 1 7 4 15 0 39 255 255), good := (rows 235 235 239 200 192 224 192 192) }] }

theorem profile19_node51 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,17] 6 194 profile19_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,17] 6 194 profile19_node51_cert).mp (by decide +kernel))

def profile19_node52_cert : CutBound 8 := { lost := (rows 0 144 128 16 0 0 0 0), upper := (rows 49 67 22 201 209 225 64 128), lower := (rows 49 67 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 238 200 192 224 192 192) },{ target := 7, region := (rows 1 3 5 8 16 32 255 0), good := (rows 119 71 86 72 80 96 64 64) }] }

theorem profile19_node52 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,18] 6 193 profile19_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,18] 6 193 profile19_node52_cert).mp (by decide +kernel))

def profile19_node53_cert : CutBound 8 := { lost := (rows 0 16 16 1 0 0 0 0), upper := (rows 49 67 69 154 146 178 64 128), lower := (rows 49 67 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 240 250 196 200 208 224 192 192) },{ target := 4, region := (rows 1 7 7 8 0 32 255 255), good := (rows 231 199 199 200 192 224 192 192) }] }

theorem profile19_node53 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,65] 6 146 profile19_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,65] 6 146 profile19_node53_cert).mp (by decide +kernel))

def profile19_node54_cert : CutBound 8 := { lost := (rows 0 16 17 0 0 0 0 0), upper := (rows 49 67 70 153 145 177 64 128), lower := (rows 49 67 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 240 198 198 200 208 224 192 192) },{ target := 4, region := (rows 1 3 7 8 0 32 255 255), good := (rows 231 199 198 200 192 224 192 192) }] }

theorem profile19_node54 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,66] 6 145 profile19_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,66] 6 145 profile19_node54_cert).mp (by decide +kernel))

def profile19_node55_cert : CutBound 8 := { lost := (rows 0 16 1 16 0 0 0 0), upper := (rows 49 67 84 139 147 163 64 128), lower := (rows 49 67 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 244 198 212 200 212 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile19_node55 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,80] 6 131 profile19_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,80] 6 131 profile19_node55_cert).mp (by decide +kernel))

def profile19_node56_cert : CutBound 8 := { lost := (rows 0 16 16 1 0 0 0 0), upper := (rows 49 67 133 218 210 242 64 128), lower := (rows 49 67 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 240 250 196 200 208 224 192 192) },{ target := 4, region := (rows 1 7 7 8 0 32 255 255), good := (rows 231 199 199 200 192 224 192 192) }] }

theorem profile19_node56 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,129] 6 210 profile19_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,129] 6 210 profile19_node56_cert).mp (by decide +kernel))

def profile19_node57_cert : CutBound 8 := { lost := (rows 0 16 17 0 0 0 0 0), upper := (rows 49 67 134 217 209 241 64 128), lower := (rows 49 67 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 240 198 198 200 208 224 192 192) },{ target := 4, region := (rows 1 3 7 8 0 32 255 255), good := (rows 231 199 198 200 192 224 192 192) }] }

theorem profile19_node57 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,130] 6 209 profile19_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,130] 6 209 profile19_node57_cert).mp (by decide +kernel))

def profile19_node58_cert : CutBound 8 := { lost := (rows 0 16 1 16 0 0 0 0), upper := (rows 49 67 148 203 211 227 64 128), lower := (rows 49 67 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 244 198 212 200 212 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile19_node58 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,144] 6 195 profile19_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,144] 6 195 profile19_node58_cert).mp (by decide +kernel))

def profile19_node59_cert : CutBound 8 := { lost := (rows 0 16 17 0 0 0 0 0), upper := (rows 49 67 196 155 147 179 64 128), lower := (rows 49 67 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 244 198 196 204 212 228 196 196) },{ target := 4, region := (rows 1 3 255 8 0 32 255 255), good := (rows 231 199 196 204 196 228 196 196) }] }

theorem profile19_node59 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,192] 6 147 profile19_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65,192] 6 147 profile19_node59_cert).mp (by decide +kernel))

def profile19_node49_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node49_route : Route 8 := (fun mask => (mask,id))

theorem profile19_node49 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,65] 6 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] profile19_node49_route profile19_node49_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node50
  · exact profile19_node51
  · exact profile19_node52
  · exact profile19_node53
  · exact profile19_node54
  · exact profile19_node55
  · exact profile19_node56
  · exact profile19_node57
  · exact profile19_node58
  · exact profile19_node59

def profile19_node61_cert : CutBound 8 := { lost := (rows 0 129 128 16 0 0 0 0), upper := (rows 49 82 7 201 209 225 64 128), lower := (rows 49 82 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 242 210 198 200 210 224 192 192) },{ target := 4, region := (rows 1 2 4 13 0 37 255 255), good := (rows 233 194 239 200 192 224 192 192) },{ target := 7, region := (rows 1 19 5 8 16 32 255 0), good := (rows 119 82 71 72 82 96 64 64) }] }

theorem profile19_node61 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,3] 6 193 profile19_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,3] 6 193 profile19_node61_cert).mp (by decide +kernel))

def profile19_node62_cert : CutBound 8 := { lost := (rows 64 1 16 64 0 0 0 0), upper := (rows 49 82 69 139 147 163 64 128), lower := (rows 49 82 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 242 210 198 200 210 224 192 192) },{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 229 194 197 200 192 224 192 192) },{ target := 6, region := (rows 3 2 4 10 18 34 0 255), good := (rows 177 187 133 136 144 160 128 128) }] }

theorem profile19_node62 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,65] 6 131 profile19_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,65] 6 131 profile19_node62_cert).mp (by decide +kernel))

def profile19_node63_cert : CutBound 8 := { lost := (rows 0 1 17 16 0 0 0 0), upper := (rows 49 82 70 137 145 161 64 128), lower := (rows 49 82 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 255 255), good := (rows 246 214 198 200 214 224 192 192) },{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 198 198 200 192 224 192 192) }] }

theorem profile19_node63 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,66] 6 129 profile19_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,66] 6 129 profile19_node63_cert).mp (by decide +kernel))

def profile19_node64_cert : CutBound 8 := { lost := (rows 0 1 80 0 0 0 0 0), upper := (rows 49 82 133 203 211 227 64 128), lower := (rows 49 82 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 242 210 198 200 210 224 192 192) },{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 229 194 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 181 146 133 136 144 160 128 128) }] }

theorem profile19_node64 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,129] 6 195 profile19_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,129] 6 195 profile19_node64_cert).mp (by decide +kernel))

def profile19_node65_cert : CutBound 8 := { lost := (rows 0 1 17 16 0 0 0 0), upper := (rows 49 82 134 201 209 225 64 128), lower := (rows 49 82 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 255 255), good := (rows 246 214 198 200 214 224 192 192) },{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 198 198 200 192 224 192 192) }] }

theorem profile19_node65 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,130] 6 193 profile19_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,130] 6 193 profile19_node65_cert).mp (by decide +kernel))

def profile19_node66_cert : CutBound 8 := { lost := (rows 0 1 17 0 0 0 0 0), upper := (rows 49 82 196 139 147 163 64 128), lower := (rows 49 82 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 255 8 16 32 255 255), good := (rows 246 214 196 204 214 228 196 196) },{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 229 198 196 204 196 228 196 196) }] }

theorem profile19_node66 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,192] 6 131 profile19_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80,192] 6 131 profile19_node66_cert).mp (by decide +kernel))

def profile19_node60_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node60_route : Route 8 := (fun mask => (mask,id))

theorem profile19_node60 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,80] 6 (by decide) (choices 2) [3,65,66,129,130,192] profile19_node60_route profile19_node60_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node61
  · exact profile19_node62
  · exact profile19_node63
  · exact profile19_node64
  · exact profile19_node65
  · exact profile19_node66

def profile19_node68_cert : CutBound 8 := { lost := (rows 0 17 16 0 0 0 0 0), upper := (rows 49 194 7 217 209 241 64 128), lower := (rows 49 194 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 242 194 198 202 210 226 194 194) },{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 231 194 199 202 194 226 194 194) }] }

theorem profile19_node68 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,3] 6 209 profile19_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,3] 6 209 profile19_node68_cert).mp (by decide +kernel))

def profile19_node69_cert : CutBound 8 := { lost := (rows 0 17 0 16 0 0 0 0), upper := (rows 49 194 21 203 211 227 64 128), lower := (rows 49 194 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 242 194 214 202 210 226 194 194) },{ target := 4, region := (rows 1 255 4 13 0 37 255 255), good := (rows 235 194 239 202 194 226 194 194) }] }

theorem profile19_node69 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,17] 6 195 profile19_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,17] 6 195 profile19_node69_cert).mp (by decide +kernel))

def profile19_node70_cert : CutBound 8 := { lost := (rows 0 17 1 16 0 0 0 0), upper := (rows 49 194 22 201 209 225 64 128), lower := (rows 49 194 22 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 21 8 16 32 255 255), good := (rows 246 194 214 202 214 226 194 194) },{ target := 4, region := (rows 1 255 4 9 0 33 255 255), good := (rows 235 194 198 202 194 226 194 194) }] }

theorem profile19_node70 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,18] 6 193 profile19_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,18] 6 193 profile19_node70_cert).mp (by decide +kernel))

def profile19_node71_cert : CutBound 8 := { lost := (rows 0 17 16 0 0 0 0 0), upper := (rows 49 194 69 155 147 179 64 128), lower := (rows 49 194 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 242 194 198 202 210 226 194 194) },{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 231 194 199 202 194 226 194 194) }] }

theorem profile19_node71 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,65] 6 147 profile19_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,65] 6 147 profile19_node71_cert).mp (by decide +kernel))

def profile19_node72_cert : CutBound 8 := { lost := (rows 0 17 17 0 0 0 0 0), upper := (rows 49 194 70 153 145 177 64 128), lower := (rows 49 194 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 32 255 255), good := (rows 246 198 198 206 214 230 198 198) },{ target := 4, region := (rows 1 255 255 8 0 32 255 255), good := (rows 231 198 198 206 198 230 198 198) }] }

theorem profile19_node72 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,66] 6 145 profile19_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,66] 6 145 profile19_node72_cert).mp (by decide +kernel))

def profile19_node73_cert : CutBound 8 := { lost := (rows 0 17 1 16 0 0 0 0), upper := (rows 49 194 84 139 147 163 64 128), lower := (rows 49 194 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 21 8 16 32 255 255), good := (rows 246 194 214 202 214 226 194 194) },{ target := 4, region := (rows 1 255 4 9 0 33 255 255), good := (rows 235 194 198 202 194 226 194 194) }] }

theorem profile19_node73 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,80] 6 131 profile19_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,80] 6 131 profile19_node73_cert).mp (by decide +kernel))

def profile19_node74_cert : CutBound 8 := { lost := (rows 0 17 17 0 0 0 0 0), upper := (rows 49 194 196 27 19 51 64 128), lower := (rows 49 194 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 32 255 255), good := (rows 246 198 198 206 214 230 198 198) },{ target := 4, region := (rows 1 255 255 8 0 32 255 255), good := (rows 231 198 198 206 198 230 198 198) }] }

theorem profile19_node74 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,192] 6 19 profile19_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192,192] 6 19 profile19_node74_cert).mp (by decide +kernel))

def profile19_node67_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node67_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node67 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48,192] 6 (by decide) (choices 2) [3,17,18,65,66,80,192] profile19_node67_route profile19_node67_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node68
  · exact profile19_node69
  · exact profile19_node70
  · exact profile19_node71
  · exact profile19_node72
  · exact profile19_node73
  · exact profile19_node74

def profile19_node47_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node47_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node47 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [48] 6 (by decide) (choices 2) [17,65,80,192] profile19_node47_route profile19_node47_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node48
  · exact profile19_node49
  · exact profile19_node60
  · exact profile19_node67

def profile19_node76_cert : CutBound 8 := { lost := (rows 144 128 0 0 0 0 0 0), upper := (rows 67 19 245 249 241 241 64 128), lower := (rows 67 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 7, region := (rows 19 18 4 8 16 32 255 0), good := (rows 67 83 68 72 83 96 64 64) }] }

theorem profile19_node76 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,17] 6 241 profile19_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,17] 6 241 profile19_node76_cert).mp (by decide +kernel))

def profile19_node77_cert : CutBound 8 := { lost := (rows 144 144 0 0 0 0 0 0), upper := (rows 67 35 213 217 209 241 64 128), lower := (rows 67 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 35 34 4 8 0 32 255 255), good := (rows 195 227 196 200 192 227 192 192) },{ target := 7, region := (rows 35 34 4 8 16 32 255 0), good := (rows 67 99 68 72 80 99 64 64) }] }

theorem profile19_node77 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,33] 6 209 profile19_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,33] 6 209 profile19_node77_cert).mp (by decide +kernel))

def profile19_node79_cert : CutBound 8 := { lost := (rows 144 0 128 16 0 0 0 0), upper := (rows 67 50 21 201 209 225 64 128), lower := (rows 67 50 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 15 0 39 255 255), good := (rows 235 235 237 200 192 224 192 192) },{ target := 7, region := (rows 3 2 6 8 16 32 255 0), good := (rows 71 119 85 72 80 96 64 64) }] }

theorem profile19_node79 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,17] 6 193 profile19_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,17] 6 193 profile19_node79_cert).mp (by decide +kernel))

def profile19_node80_cert : CutBound 8 := { lost := (rows 16 64 16 64 0 0 0 0), upper := (rows 67 50 69 153 145 177 64 128), lower := (rows 67 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 255 255), good := (rows 199 231 197 200 192 224 192 192) },{ target := 6, region := (rows 1 7 4 13 21 37 0 255), good := (rows 187 178 191 136 144 160 128 128) }] }

theorem profile19_node80 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,65] 6 145 profile19_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,65] 6 145 profile19_node80_cert).mp (by decide +kernel))

def profile19_node81_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 67 50 84 137 145 161 64 128), lower := (rows 67 50 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 198 246 212 200 212 224 192 192) },{ target := 4, region := (rows 3 2 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile19_node81 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,80] 6 129 profile19_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,80] 6 129 profile19_node81_cert).mp (by decide +kernel))

def profile19_node82_cert : CutBound 8 := { lost := (rows 16 0 80 0 0 0 0 0), upper := (rows 67 50 133 217 209 241 64 128), lower := (rows 67 50 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 255 255), good := (rows 199 231 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 135 178 133 136 144 160 128 128) }] }

theorem profile19_node82 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,129] 6 209 profile19_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,129] 6 209 profile19_node82_cert).mp (by decide +kernel))

def profile19_node83_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 67 50 148 201 209 225 64 128), lower := (rows 67 50 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 198 246 212 200 212 224 192 192) },{ target := 4, region := (rows 3 2 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile19_node83 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,144] 6 193 profile19_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,144] 6 193 profile19_node83_cert).mp (by decide +kernel))

def profile19_node84_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 67 50 196 153 145 177 64 128), lower := (rows 67 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 198 246 196 204 212 228 196 196) },{ target := 4, region := (rows 3 2 255 8 0 32 255 255), good := (rows 199 231 196 204 196 228 196 196) }] }

theorem profile19_node84 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,192] 6 145 profile19_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48,192] 6 145 profile19_node84_cert).mp (by decide +kernel))

def profile19_node78_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node78_route : Route 8 := (fun mask => (mask,id))

theorem profile19_node78 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,48] 6 (by decide) (choices 2) [17,65,80,129,144,192] profile19_node78_route profile19_node78_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node79
  · exact profile19_node80
  · exact profile19_node81
  · exact profile19_node82
  · exact profile19_node83
  · exact profile19_node84

def profile19_node85_cert : CutBound 8 := { lost := (rows 16 16 64 64 0 0 0 0), upper := (rows 67 67 181 185 177 177 64 128), lower := (rows 67 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 6, region := (rows 1 2 7 11 19 35 0 255), good := (rows 191 191 132 136 144 160 128 128) }] }

theorem profile19_node85 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,65] 6 177 profile19_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,65] 6 177 profile19_node85_cert).mp (by decide +kernel))

def profile19_node86_cert : CutBound 8 := { lost := (rows 16 1 64 64 0 0 0 0), upper := (rows 67 82 181 185 177 177 64 128), lower := (rows 67 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 194 210 196 200 210 224 192 192) },{ target := 4, region := (rows 3 2 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 6, region := (rows 1 2 5 9 17 33 0 255), good := (rows 191 146 132 136 144 160 128 128) }] }

theorem profile19_node86 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,80] 6 177 profile19_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,80] 6 177 profile19_node86_cert).mp (by decide +kernel))

def profile19_node87_cert : CutBound 8 := { lost := (rows 16 17 0 0 0 0 0 0), upper := (rows 67 98 149 153 145 177 64 128), lower := (rows 67 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 194 226 196 200 208 226 192 192) },{ target := 4, region := (rows 35 34 4 8 0 32 255 255), good := (rows 195 227 196 200 192 227 192 192) }] }

theorem profile19_node87 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,96] 6 145 profile19_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,96] 6 145 profile19_node87_cert).mp (by decide +kernel))

def profile19_node88_cert : CutBound 8 := { lost := (rows 16 80 0 0 0 0 0 0), upper := (rows 67 131 245 249 241 241 64 128), lower := (rows 67 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 131 131 132 136 144 160 128 128) }] }

theorem profile19_node88 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,129] 6 241 profile19_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,129] 6 241 profile19_node88_cert).mp (by decide +kernel))

def profile19_node89_cert : CutBound 8 := { lost := (rows 16 65 0 0 0 0 0 0), upper := (rows 67 146 245 249 241 241 64 128), lower := (rows 67 146 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 194 210 196 200 210 224 192 192) },{ target := 4, region := (rows 3 2 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 6, region := (rows 1 18 4 8 16 32 0 255), good := (rows 131 146 132 136 146 160 128 128) }] }

theorem profile19_node89 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,144] 6 241 profile19_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,144] 6 241 profile19_node89_cert).mp (by decide +kernel))

def profile19_node90_cert : CutBound 8 := { lost := (rows 16 17 0 0 0 0 0 0), upper := (rows 67 162 213 217 209 241 64 128), lower := (rows 67 162 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 194 226 196 200 208 226 192 192) },{ target := 4, region := (rows 35 34 4 8 0 32 255 255), good := (rows 195 227 196 200 192 227 192 192) }] }

theorem profile19_node90 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,160] 6 209 profile19_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,160] 6 209 profile19_node90_cert).mp (by decide +kernel))

def profile19_node91_cert : CutBound 8 := { lost := (rows 16 17 0 0 0 0 0 0), upper := (rows 67 194 181 185 177 177 64 128), lower := (rows 67 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 194 194 198 202 210 226 194 194) },{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) }] }

theorem profile19_node91 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,192] 6 177 profile19_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66,192] 6 177 profile19_node91_cert).mp (by decide +kernel))

def profile19_node75_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile19_node75_route : Route 8 := (fun mask => (mask,id))

theorem profile19_node75 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [66] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile19_node75_route profile19_node75_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node76
  · exact profile19_node77
  · exact profile19_node78
  · exact profile19_node85
  · exact profile19_node86
  · exact profile19_node87
  · exact profile19_node88
  · exact profile19_node89
  · exact profile19_node90
  · exact profile19_node91

def profile19_node93_cert : CutBound 8 := { lost := (rows 0 64 16 16 0 0 0 0), upper := (rows 81 19 231 235 243 227 64 128), lower := (rows 81 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 255 255), good := (rows 193 239 196 200 192 224 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 147 147 132 136 144 160 128 128) }] }

theorem profile19_node93 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,17] 6 227 profile19_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,17] 6 227 profile19_node93_cert).mp (by decide +kernel))

def profile19_node95_cert : CutBound 8 := { lost := (rows 0 0 80 1 0 0 0 0), upper := (rows 81 35 7 216 208 240 64 128), lower := (rows 81 35 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 254 248 248 248 248 248) },{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 193 231 199 200 192 224 192 192) },{ target := 6, region := (rows 1 2 6 8 16 32 0 255), good := (rows 145 167 135 136 144 160 128 128) }] }

theorem profile19_node95 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,3] 6 208 profile19_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,3] 6 208 profile19_node95_cert).mp (by decide +kernel))

def profile19_node96_cert : CutBound 8 := { lost := (rows 0 16 0 17 0 0 0 0), upper := (rows 81 35 21 202 210 226 64 128), lower := (rows 81 35 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 208 250 212 200 208 224 192 192) },{ target := 4, region := (rows 1 7 4 15 0 39 255 255), good := (rows 235 235 239 200 192 224 192 192) }] }

theorem profile19_node96 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,17] 6 194 profile19_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,17] 6 194 profile19_node96_cert).mp (by decide +kernel))

def profile19_node97_cert : CutBound 8 := { lost := (rows 128 16 0 16 0 0 0 0), upper := (rows 81 35 22 201 209 225 64 128), lower := (rows 81 35 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 238 200 192 224 192 192) },{ target := 7, region := (rows 21 2 4 8 16 32 255 0), good := (rows 81 99 87 72 81 96 64 64) }] }

theorem profile19_node97 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,18] 6 193 profile19_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,18] 6 193 profile19_node97_cert).mp (by decide +kernel))

def profile19_node98_cert : CutBound 8 := { lost := (rows 0 64 16 65 0 0 0 0), upper := (rows 81 35 69 154 146 178 64 128), lower := (rows 81 35 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 208 250 196 200 208 224 192 192) },{ target := 4, region := (rows 1 2 7 8 0 32 255 255), good := (rows 197 231 197 200 192 224 192 192) },{ target := 6, region := (rows 1 7 4 15 23 39 0 255), good := (rows 187 187 191 136 144 160 128 128) }] }

theorem profile19_node98 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,65] 6 146 profile19_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,65] 6 146 profile19_node98_cert).mp (by decide +kernel))

def profile19_node99_cert : CutBound 8 := { lost := (rows 0 64 17 64 0 0 0 0), upper := (rows 81 35 70 153 145 177 64 128), lower := (rows 81 35 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 208 230 198 200 208 224 192 192) },{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 193 231 198 200 192 224 192 192) },{ target := 6, region := (rows 1 3 4 11 19 35 0 255), good := (rows 187 187 190 136 144 160 128 128) }] }

theorem profile19_node99 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,66] 6 145 profile19_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,66] 6 145 profile19_node99_cert).mp (by decide +kernel))

def profile19_node100_cert : CutBound 8 := { lost := (rows 0 16 1 16 0 0 0 0), upper := (rows 81 35 84 139 147 163 64 128), lower := (rows 81 35 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 212 230 212 200 212 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile19_node100 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,80] 6 131 profile19_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,80] 6 131 profile19_node100_cert).mp (by decide +kernel))

def profile19_node101_cert : CutBound 8 := { lost := (rows 0 0 80 1 0 0 0 0), upper := (rows 81 35 133 218 210 242 64 128), lower := (rows 81 35 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 208 250 196 200 208 224 192 192) },{ target := 4, region := (rows 1 2 7 8 0 32 255 255), good := (rows 197 231 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 7 8 16 32 0 255), good := (rows 149 167 133 136 144 160 128 128) }] }

theorem profile19_node101 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,129] 6 210 profile19_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,129] 6 210 profile19_node101_cert).mp (by decide +kernel))

def profile19_node102_cert : CutBound 8 := { lost := (rows 0 0 81 0 0 0 0 0), upper := (rows 81 35 134 217 209 241 64 128), lower := (rows 81 35 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 208 230 198 200 208 224 192 192) },{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 193 231 198 200 192 224 192 192) },{ target := 6, region := (rows 1 2 6 8 16 32 0 255), good := (rows 145 167 134 136 144 160 128 128) }] }

theorem profile19_node102 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,130] 6 209 profile19_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,130] 6 209 profile19_node102_cert).mp (by decide +kernel))

def profile19_node103_cert : CutBound 8 := { lost := (rows 0 16 1 16 0 0 0 0), upper := (rows 81 35 148 203 211 227 64 128), lower := (rows 81 35 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 212 230 212 200 212 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile19_node103 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,144] 6 195 profile19_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,144] 6 195 profile19_node103_cert).mp (by decide +kernel))

def profile19_node104_cert : CutBound 8 := { lost := (rows 0 64 17 64 0 0 0 0), upper := (rows 81 35 196 155 147 179 64 128), lower := (rows 81 35 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 212 230 196 204 212 228 196 196) },{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 231 196 204 196 228 196 196) },{ target := 6, region := (rows 1 3 4 11 19 35 0 255), good := (rows 187 187 132 136 144 160 128 128) }] }

theorem profile19_node104 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,192] 6 147 profile19_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33,192] 6 147 profile19_node104_cert).mp (by decide +kernel))

def profile19_node94_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node94_route : Route 8 := (fun mask => (mask,id))

theorem profile19_node94 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,33] 6 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] profile19_node94_route profile19_node94_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node95
  · exact profile19_node96
  · exact profile19_node97
  · exact profile19_node98
  · exact profile19_node99
  · exact profile19_node100
  · exact profile19_node101
  · exact profile19_node102
  · exact profile19_node103
  · exact profile19_node104

def profile19_node106_cert : CutBound 8 := { lost := (rows 128 0 128 16 0 0 0 0), upper := (rows 81 50 7 201 209 225 64 128), lower := (rows 81 50 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 13 0 37 255 255), good := (rows 233 226 239 200 192 224 192 192) },{ target := 7, region := (rows 19 2 6 8 16 32 255 0), good := (rows 81 119 71 72 81 96 64 64) }] }

theorem profile19_node106 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,3] 6 193 profile19_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,3] 6 193 profile19_node106_cert).mp (by decide +kernel))

def profile19_node107_cert : CutBound 8 := { lost := (rows 0 64 16 64 0 0 0 0), upper := (rows 81 50 69 139 147 163 64 128), lower := (rows 81 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 197 226 197 200 192 224 192 192) },{ target := 6, region := (rows 1 7 4 13 21 37 0 255), good := (rows 187 178 191 136 144 160 128 128) }] }

theorem profile19_node107 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,65] 6 131 profile19_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,65] 6 131 profile19_node107_cert).mp (by decide +kernel))

def profile19_node108_cert : CutBound 8 := { lost := (rows 0 0 17 16 0 0 0 0), upper := (rows 81 50 70 137 145 161 64 128), lower := (rows 81 50 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 208 246 198 200 208 224 192 192) },{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 230 198 200 192 224 192 192) }] }

theorem profile19_node108 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,66] 6 129 profile19_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,66] 6 129 profile19_node108_cert).mp (by decide +kernel))

def profile19_node109_cert : CutBound 8 := { lost := (rows 128 0 80 0 0 0 0 0), upper := (rows 81 50 133 203 211 227 64 128), lower := (rows 81 50 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 197 226 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 149 178 133 136 144 160 128 128) },{ target := 7, region := (rows 19 2 4 8 16 32 255 0), good := (rows 81 115 69 72 81 96 64 64) }] }

theorem profile19_node109 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,129] 6 195 profile19_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,129] 6 195 profile19_node109_cert).mp (by decide +kernel))

def profile19_node110_cert : CutBound 8 := { lost := (rows 0 0 17 16 0 0 0 0), upper := (rows 81 50 134 201 209 225 64 128), lower := (rows 81 50 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 208 246 198 200 208 224 192 192) },{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 230 198 200 192 224 192 192) }] }

theorem profile19_node110 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,130] 6 193 profile19_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,130] 6 193 profile19_node110_cert).mp (by decide +kernel))

def profile19_node111_cert : CutBound 8 := { lost := (rows 0 64 17 64 0 0 0 0), upper := (rows 81 50 196 139 147 163 64 128), lower := (rows 81 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 212 246 196 204 212 228 196 196) },{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 230 196 204 196 228 196 196) },{ target := 6, region := (rows 1 3 4 9 17 33 0 255), good := (rows 187 178 132 136 144 160 128 128) }] }

theorem profile19_node111 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,192] 6 131 profile19_node111_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48,192] 6 131 profile19_node111_cert).mp (by decide +kernel))

def profile19_node105_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node105_route : Route 8 := (fun mask => (mask,id))

theorem profile19_node105 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,48] 6 (by decide) (choices 2) [3,65,66,129,130,192] profile19_node105_route profile19_node105_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node106
  · exact profile19_node107
  · exact profile19_node108
  · exact profile19_node109
  · exact profile19_node110
  · exact profile19_node111

def profile19_node112_cert : CutBound 8 := { lost := (rows 0 16 64 64 0 0 0 0), upper := (rows 81 67 183 187 179 179 64 128), lower := (rows 81 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 6, region := (rows 1 2 6 10 18 34 0 255), good := (rows 145 191 132 136 144 160 128 128) }] }

theorem profile19_node112 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,65] 6 179 profile19_node112_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,65] 6 179 profile19_node112_cert).mp (by decide +kernel))

def profile19_node113_cert : CutBound 8 := { lost := (rows 128 129 0 0 0 0 0 0), upper := (rows 81 82 167 171 179 163 64 128), lower := (rows 81 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 210 210 196 200 210 224 192 192) },{ target := 7, region := (rows 19 19 4 8 16 32 255 0), good := (rows 83 83 68 72 83 96 64 64) }] }

theorem profile19_node113 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,80] 6 163 profile19_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,80] 6 163 profile19_node113_cert).mp (by decide +kernel))

def profile19_node114_cert : CutBound 8 := { lost := (rows 128 145 0 0 0 0 0 0), upper := (rows 81 98 151 155 147 179 64 128), lower := (rows 81 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 208 226 196 200 208 226 192 192) },{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) },{ target := 7, region := (rows 17 34 4 8 16 32 255 0), good := (rows 81 98 68 72 81 98 64 64) }] }

theorem profile19_node114 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,96] 6 147 profile19_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,96] 6 147 profile19_node114_cert).mp (by decide +kernel))

def profile19_node115_cert : CutBound 8 := { lost := (rows 128 80 0 0 0 0 0 0), upper := (rows 81 131 247 251 243 243 64 128), lower := (rows 81 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 147 131 132 136 144 160 128 128) },{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 67 68 72 81 96 64 64) }] }

theorem profile19_node115 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,129] 6 243 profile19_node115_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,129] 6 243 profile19_node115_cert).mp (by decide +kernel))

def profile19_node116_cert : CutBound 8 := { lost := (rows 128 65 0 0 0 0 0 0), upper := (rows 81 146 231 235 243 227 64 128), lower := (rows 81 146 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 210 210 196 200 210 224 192 192) },{ target := 6, region := (rows 1 19 4 8 16 32 0 255), good := (rows 147 146 132 136 146 160 128 128) },{ target := 7, region := (rows 19 2 4 8 16 32 255 0), good := (rows 81 83 68 72 81 96 64 64) }] }

theorem profile19_node116 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,144] 6 227 profile19_node116_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,144] 6 227 profile19_node116_cert).mp (by decide +kernel))

def profile19_node117_cert : CutBound 8 := { lost := (rows 0 81 0 0 0 0 0 0), upper := (rows 81 162 215 219 211 243 64 128), lower := (rows 81 162 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 208 226 196 200 208 226 192 192) },{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) },{ target := 6, region := (rows 1 34 4 8 16 32 0 255), good := (rows 145 162 132 136 144 162 128 128) }] }

theorem profile19_node117 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,160] 6 211 profile19_node117_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,160] 6 211 profile19_node117_cert).mp (by decide +kernel))

def profile19_node118_cert : CutBound 8 := { lost := (rows 128 17 0 0 0 0 0 0), upper := (rows 81 194 183 187 179 179 64 128), lower := (rows 81 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 210 194 198 202 210 226 194 194) },{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 195 194 198 202 194 226 194 194) },{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 66 68 72 81 96 64 64) }] }

theorem profile19_node118 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,192] 6 179 profile19_node118_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80,192] 6 179 profile19_node118_cert).mp (by decide +kernel))

def profile19_node92_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile19_node92_route : Route 8 := (fun mask => (mask,id))

theorem profile19_node92 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [80] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile19_node92_route profile19_node92_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node93
  · exact profile19_node94
  · exact profile19_node105
  · exact profile19_node112
  · exact profile19_node113
  · exact profile19_node114
  · exact profile19_node115
  · exact profile19_node116
  · exact profile19_node117
  · exact profile19_node118

def profile19_node121_cert : CutBound 8 := { lost := (rows 16 0 16 1 0 0 0 0), upper := (rows 97 19 7 216 208 240 64 128), lower := (rows 97 19 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 254 248 248 248 248 248) },{ target := 4, region := (rows 33 2 6 8 0 32 255 255), good := (rows 225 199 199 200 192 225 192 192) }] }

theorem profile19_node121 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,3] 6 208 profile19_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,3] 6 208 profile19_node121_cert).mp (by decide +kernel))

def profile19_node122_cert : CutBound 8 := { lost := (rows 16 0 0 17 0 0 0 0), upper := (rows 97 19 21 202 210 226 64 128), lower := (rows 97 19 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 224 250 212 200 208 224 192 192) },{ target := 4, region := (rows 35 2 4 10 0 34 255 255), good := (rows 225 235 197 200 192 225 192 192) }] }

theorem profile19_node122 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,17] 6 194 profile19_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,17] 6 194 profile19_node122_cert).mp (by decide +kernel))

def profile19_node123_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 97 19 22 201 209 225 64 128), lower := (rows 97 19 22 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 224 214 214 200 208 224 192 192) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 239 233 233 233 233 233) }] }

theorem profile19_node123 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,18] 6 193 profile19_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,18] 6 193 profile19_node123_cert).mp (by decide +kernel))

def profile19_node124_cert : CutBound 8 := { lost := (rows 16 0 16 1 0 0 0 0), upper := (rows 97 19 69 154 146 178 64 128), lower := (rows 97 19 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 224 250 196 200 208 224 192 192) },{ target := 4, region := (rows 33 2 39 8 0 32 255 255), good := (rows 229 199 197 200 192 229 192 192) }] }

theorem profile19_node124 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,65] 6 146 profile19_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,65] 6 146 profile19_node124_cert).mp (by decide +kernel))

def profile19_node125_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 97 19 70 153 145 177 64 128), lower := (rows 97 19 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 224 214 198 200 208 224 192 192) },{ target := 4, region := (rows 33 2 6 8 0 32 255 255), good := (rows 225 199 198 200 192 225 192 192) }] }

theorem profile19_node125 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,66] 6 145 profile19_node125_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,66] 6 145 profile19_node125_cert).mp (by decide +kernel))

def profile19_node126_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 97 19 84 139 147 163 64 128), lower := (rows 97 19 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 224 214 212 200 212 224 192 192) },{ target := 4, region := (rows 35 2 4 10 0 34 255 255), good := (rows 225 235 196 200 192 225 192 192) }] }

theorem profile19_node126 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,80] 6 131 profile19_node126_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,80] 6 131 profile19_node126_cert).mp (by decide +kernel))

def profile19_node127_cert : CutBound 8 := { lost := (rows 16 0 16 1 0 0 0 0), upper := (rows 97 19 133 218 210 242 64 128), lower := (rows 97 19 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 224 250 196 200 208 224 192 192) },{ target := 4, region := (rows 33 2 39 8 0 32 255 255), good := (rows 229 199 197 200 192 229 192 192) }] }

theorem profile19_node127 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,129] 6 210 profile19_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,129] 6 210 profile19_node127_cert).mp (by decide +kernel))

def profile19_node128_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 97 19 134 217 209 241 64 128), lower := (rows 97 19 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 224 214 198 200 208 224 192 192) },{ target := 4, region := (rows 33 2 6 8 0 32 255 255), good := (rows 225 199 198 200 192 225 192 192) }] }

theorem profile19_node128 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,130] 6 209 profile19_node128_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,130] 6 209 profile19_node128_cert).mp (by decide +kernel))

def profile19_node129_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 97 19 148 203 211 227 64 128), lower := (rows 97 19 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 224 214 212 200 212 224 192 192) },{ target := 4, region := (rows 35 2 4 10 0 34 255 255), good := (rows 225 235 196 200 192 225 192 192) }] }

theorem profile19_node129 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,144] 6 195 profile19_node129_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,144] 6 195 profile19_node129_cert).mp (by decide +kernel))

def profile19_node130_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 97 19 196 155 147 179 64 128), lower := (rows 97 19 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 228 214 196 204 212 228 196 196) },{ target := 4, region := (rows 33 2 255 8 0 32 255 255), good := (rows 229 199 196 204 196 229 196 196) }] }

theorem profile19_node130 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,192] 6 147 profile19_node130_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17,192] 6 147 profile19_node130_cert).mp (by decide +kernel))


#print axioms profile19_node130
end Delivery.SmallBudgetTenFinite8
