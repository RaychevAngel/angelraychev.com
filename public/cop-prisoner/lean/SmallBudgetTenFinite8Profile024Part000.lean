import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile24_node2_cert : CutBound 8 := { lost := (rows 32 32 16 16 0 0 0 0), upper := (rows 19 19 228 232 240 224 64 128), lower := (rows 19 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 239 239 236 236 236 236 236 236) },{ target := 5, region := (rows 19 19 4 8 16 0 255 255), good := (rows 211 211 196 200 211 192 192 192) }] }

theorem profile24_node2 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,17] 6 224 profile24_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,17] 6 224 profile24_node2_cert).mp (by decide +kernel))

def profile24_node4_cert : CutBound 8 := { lost := (rows 32 16 0 48 0 0 0 0), upper := (rows 19 35 52 200 208 224 64 128), lower := (rows 19 35 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 255 0 255 255 255), good := (rows 235 235 236 232 232 232 232 232) },{ target := 5, region := (rows 3 2 4 255 255 0 255 255), good := (rows 219 219 220 216 216 216 216 216) }] }

theorem profile24_node4 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,48] 6 192 profile24_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,48] 6 192 profile24_node4_cert).mp (by decide +kernel))

def profile24_node5_cert : CutBound 8 := { lost := (rows 0 16 160 16 0 0 0 0), upper := (rows 19 35 84 232 240 224 64 128), lower := (rows 19 35 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 255 0 255 255 255), good := (rows 235 235 236 232 232 232 232 232) },{ target := 5, region := (rows 1 2 21 8 16 0 255 255), good := (rows 215 199 212 200 212 192 192 192) },{ target := 7, region := (rows 1 2 21 8 16 32 255 0), good := (rows 87 103 84 72 84 96 64 64) }] }

theorem profile24_node5 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,80] 6 224 profile24_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,80] 6 224 profile24_node5_cert).mp (by decide +kernel))

def profile24_node6_cert : CutBound 8 := { lost := (rows 32 0 144 32 0 0 0 0), upper := (rows 19 35 100 216 208 240 64 128), lower := (rows 19 35 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 255 255), good := (rows 199 231 228 200 192 228 192 192) },{ target := 5, region := (rows 3 2 4 255 255 0 255 255), good := (rows 219 219 220 216 216 216 216 216) },{ target := 7, region := (rows 1 2 38 8 16 32 255 0), good := (rows 87 103 100 72 80 100 64 64) }] }

theorem profile24_node6 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,96] 6 208 profile24_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,96] 6 208 profile24_node6_cert).mp (by decide +kernel))

def profile24_node8_cert : CutBound 8 := { lost := (rows 32 16 48 0 0 0 0 0), upper := (rows 19 35 196 56 208 224 64 128), lower := (rows 19 35 196 56 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 255 8 0 255 255 255), good := (rows 231 231 228 236 228 228 228 228) },{ target := 5, region := (rows 3 2 255 8 255 0 255 255), good := (rows 215 215 212 220 212 212 212 212) }] }

theorem profile24_node8 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,48] 6 192 profile24_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,48] 6 192 profile24_node8_cert).mp (by decide +kernel))

def profile24_node9_cert : CutBound 8 := { lost := (rows 0 16 48 32 0 0 0 0), upper := (rows 19 35 196 88 176 160 64 128), lower := (rows 19 35 196 88 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 255 8 0 255 255 255), good := (rows 231 231 228 236 228 228 228 228) },{ target := 5, region := (rows 1 2 255 25 16 0 255 255), good := (rows 223 207 196 220 220 196 196 196) }] }

theorem profile24_node9 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,80] 6 160 profile24_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,80] 6 160 profile24_node9_cert).mp (by decide +kernel))

def profile24_node10_cert : CutBound 8 := { lost := (rows 32 0 48 16 0 0 0 0), upper := (rows 19 35 196 104 144 176 64 128), lower := (rows 19 35 196 104 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 42 0 32 255 255), good := (rows 207 239 196 236 196 236 196 196) },{ target := 5, region := (rows 3 2 255 8 255 0 255 255), good := (rows 215 215 212 220 212 212 212 212) }] }

theorem profile24_node10 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,96] 6 144 profile24_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,96] 6 144 profile24_node10_cert).mp (by decide +kernel))

def profile24_node11_cert : CutBound 8 := { lost := (rows 0 0 48 48 0 0 0 0), upper := (rows 19 35 196 200 48 48 64 128), lower := (rows 19 35 196 200 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 32 255 255), good := (rows 207 239 204 204 204 236 204 204) },{ target := 5, region := (rows 1 2 255 255 16 0 255 255), good := (rows 223 207 204 204 220 204 204 204) }] }

theorem profile24_node11 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,192] 6 48 profile24_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192,192] 6 48 profile24_node11_cert).mp (by decide +kernel))

def profile24_node7_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile24_node7_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node7 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33,192] 6 (by decide) (choices 2) [48,80,96,192] profile24_node7_route profile24_node7_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile24_node8
  · exact profile24_node9
  · exact profile24_node10
  · exact profile24_node11

def profile24_node3_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node3_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node3 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,33] 6 (by decide) (choices 2) [48,80,96,192] profile24_node3_route profile24_node3_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile24_node4
  · exact profile24_node5
  · exact profile24_node6
  · exact profile24_node7

def profile24_node12_cert : CutBound 8 := { lost := (rows 96 0 16 16 0 0 0 0), upper := (rows 19 50 229 233 241 225 64 128), lower := (rows 19 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 239 226 196 200 192 224 192 192) },{ target := 5, region := (rows 3 2 4 8 16 0 255 255), good := (rows 211 211 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 8 16 32 0 255), good := (rows 147 179 132 136 144 160 128 128) }] }

theorem profile24_node12 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,48] 6 225 profile24_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,48] 6 225 profile24_node12_cert).mp (by decide +kernel))

def profile24_node13_cert : CutBound 8 := { lost := (rows 160 176 0 0 0 0 0 0), upper := (rows 19 67 244 248 240 240 64 128), lower := (rows 19 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 5, region := (rows 17 19 4 8 16 0 255 255), good := (rows 211 195 196 200 211 192 192 192) },{ target := 7, region := (rows 17 19 4 8 16 32 255 0), good := (rows 83 67 68 72 83 96 64 64) }] }

theorem profile24_node13 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,65] 6 240 profile24_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,65] 6 240 profile24_node13_cert).mp (by decide +kernel))

def profile24_node14_cert : CutBound 8 := { lost := (rows 32 32 16 16 0 0 0 0), upper := (rows 19 82 229 233 241 225 64 128), lower := (rows 19 82 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 239 194 196 200 192 224 192 192) },{ target := 5, region := (rows 19 19 4 8 16 0 255 255), good := (rows 211 211 196 200 211 192 192 192) }] }

theorem profile24_node14 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,80] 6 225 profile24_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,80] 6 225 profile24_node14_cert).mp (by decide +kernel))

def profile24_node16_cert : CutBound 8 := { lost := (rows 0 16 96 16 0 0 0 0), upper := (rows 19 98 21 232 240 224 64 128), lower := (rows 19 98 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 239 234 234 234 234 234) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 215 194 213 200 208 192 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 151 162 149 136 144 160 128 128) }] }

theorem profile24_node16 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,17] 6 224 profile24_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,17] 6 224 profile24_node16_cert).mp (by decide +kernel))

def profile24_node17_cert : CutBound 8 := { lost := (rows 32 144 0 32 0 0 0 0), upper := (rows 19 98 37 216 208 240 64 128), lower := (rows 19 98 37 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 38 4 8 0 32 255 255), good := (rows 195 226 231 200 192 226 192 192) },{ target := 5, region := (rows 3 2 4 255 255 0 255 255), good := (rows 219 219 221 216 216 216 216 216) },{ target := 7, region := (rows 1 38 4 8 16 32 255 0), good := (rows 83 98 103 72 80 98 64 64) }] }

theorem profile24_node17 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,33] 6 208 profile24_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,33] 6 208 profile24_node17_cert).mp (by decide +kernel))

def profile24_node18_cert : CutBound 8 := { lost := (rows 32 16 0 48 0 0 0 0), upper := (rows 19 98 52 201 209 225 64 128), lower := (rows 19 98 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 39 4 9 0 33 255 255), good := (rows 235 226 230 200 192 226 192 192) },{ target := 5, region := (rows 3 2 4 11 19 0 255 255), good := (rows 219 219 212 200 208 192 192 192) }] }

theorem profile24_node18 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,48] 6 193 profile24_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,48] 6 193 profile24_node18_cert).mp (by decide +kernel))

def profile24_node19_cert : CutBound 8 := { lost := (rows 64 16 48 64 0 0 0 0), upper := (rows 19 98 69 184 176 176 64 128), lower := (rows 19 98 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 5 8 0 32 255 255), good := (rows 199 226 197 200 192 226 192 192) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 215 194 197 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 255 255 255 0 255), good := (rows 187 187 189 184 184 184 184 184) }] }

theorem profile24_node19 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,65] 6 176 profile24_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,65] 6 176 profile24_node19_cert).mp (by decide +kernel))

def profile24_node20_cert : CutBound 8 := { lost := (rows 64 16 32 80 0 0 0 0), upper := (rows 19 98 84 169 177 161 64 128), lower := (rows 19 98 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 35 4 9 0 33 255 255), good := (rows 235 226 196 200 192 226 192 192) },{ target := 5, region := (rows 1 2 21 8 16 0 255 255), good := (rows 215 194 212 200 212 192 192 192) },{ target := 6, region := (rows 3 2 4 11 19 35 0 255), good := (rows 187 187 148 136 144 160 128 128) }] }

theorem profile24_node20 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,80] 6 161 profile24_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,80] 6 161 profile24_node20_cert).mp (by decide +kernel))

def profile24_node21_cert : CutBound 8 := { lost := (rows 32 16 16 32 0 0 0 0), upper := (rows 19 98 100 153 145 177 64 128), lower := (rows 19 98 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 38 38 8 0 32 255 255), good := (rows 199 230 230 200 192 230 192 192) },{ target := 5, region := (rows 3 2 4 11 19 0 255 255), good := (rows 219 219 196 200 208 192 192 192) }] }

theorem profile24_node21 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,96] 6 145 profile24_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,96] 6 145 profile24_node21_cert).mp (by decide +kernel))

def profile24_node22_cert : CutBound 8 := { lost := (rows 0 16 112 0 0 0 0 0), upper := (rows 19 98 133 248 240 240 64 128), lower := (rows 19 98 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 5 8 0 32 255 255), good := (rows 199 226 197 200 192 226 192 192) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 215 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 151 162 133 136 144 160 128 128) }] }

theorem profile24_node22 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,129] 6 240 profile24_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,129] 6 240 profile24_node22_cert).mp (by decide +kernel))

def profile24_node23_cert : CutBound 8 := { lost := (rows 0 16 96 16 0 0 0 0), upper := (rows 19 98 148 233 241 225 64 128), lower := (rows 19 98 148 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 35 4 9 0 33 255 255), good := (rows 235 226 196 200 192 226 192 192) },{ target := 5, region := (rows 1 2 21 8 16 0 255 255), good := (rows 215 194 212 200 212 192 192 192) },{ target := 6, region := (rows 1 2 21 8 16 32 0 255), good := (rows 151 162 148 136 148 160 128 128) }] }

theorem profile24_node23 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,144] 6 225 profile24_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,144] 6 225 profile24_node23_cert).mp (by decide +kernel))

def profile24_node24_cert : CutBound 8 := { lost := (rows 32 16 16 32 0 0 0 0), upper := (rows 19 98 164 217 209 241 64 128), lower := (rows 19 98 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 38 38 8 0 32 255 255), good := (rows 199 230 230 200 192 230 192 192) },{ target := 5, region := (rows 3 2 4 11 19 0 255 255), good := (rows 219 219 196 200 208 192 192 192) }] }

theorem profile24_node24 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,160] 6 209 profile24_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,160] 6 209 profile24_node24_cert).mp (by decide +kernel))

def profile24_node25_cert : CutBound 8 := { lost := (rows 64 16 48 64 0 0 0 0), upper := (rows 19 98 196 185 177 177 64 128), lower := (rows 19 98 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 255 8 0 32 255 255), good := (rows 199 230 196 204 196 230 196 196) },{ target := 5, region := (rows 1 2 255 8 16 0 255 255), good := (rows 215 198 196 204 212 196 196 196) },{ target := 6, region := (rows 3 2 4 11 19 35 0 255), good := (rows 187 187 132 136 144 160 128 128) }] }

theorem profile24_node25 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,192] 6 177 profile24_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96,192] 6 177 profile24_node25_cert).mp (by decide +kernel))

def profile24_node15_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node15_route : Route 8 := (fun mask => (mask,id))

theorem profile24_node15 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,96] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile24_node15_route profile24_node15_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node16
  · exact profile24_node17
  · exact profile24_node18
  · exact profile24_node19
  · exact profile24_node20
  · exact profile24_node21
  · exact profile24_node22
  · exact profile24_node23
  · exact profile24_node24
  · exact profile24_node25

def profile24_node27_cert : CutBound 8 := { lost := (rows 32 48 32 16 0 0 0 0), upper := (rows 19 194 21 232 240 224 64 128), lower := (rows 19 194 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 239 234 234 234 234 234) },{ target := 5, region := (rows 21 255 21 8 16 0 255 255), good := (rows 215 194 215 202 215 194 194 194) }] }

theorem profile24_node27 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,17] 6 224 profile24_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,17] 6 224 profile24_node27_cert).mp (by decide +kernel))

def profile24_node29_cert : CutBound 8 := { lost := (rows 32 48 16 0 0 0 0 0), upper := (rows 19 194 37 56 208 224 64 128), lower := (rows 19 194 37 56 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 255 255 255), good := (rows 231 226 231 234 226 226 226 226) },{ target := 5, region := (rows 255 255 4 8 255 0 255 255), good := (rows 211 211 215 219 211 211 211 211) }] }

theorem profile24_node29 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,48] 6 192 profile24_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,48] 6 192 profile24_node29_cert).mp (by decide +kernel))

def profile24_node30_cert : CutBound 8 := { lost := (rows 32 48 16 32 0 0 0 0), upper := (rows 19 194 37 88 176 160 64 128), lower := (rows 19 194 37 88 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 255 255 255), good := (rows 231 226 231 234 226 226 226 226) },{ target := 5, region := (rows 25 255 4 25 16 0 255 255), good := (rows 219 194 207 219 219 194 194 194) }] }

theorem profile24_node30 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,80] 6 160 profile24_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,80] 6 160 profile24_node30_cert).mp (by decide +kernel))

def profile24_node31_cert : CutBound 8 := { lost := (rows 32 48 0 16 0 0 0 0), upper := (rows 19 194 37 104 144 176 64 128), lower := (rows 19 194 37 104 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 44 0 32 255 255), good := (rows 195 194 239 234 194 234 194 194) },{ target := 5, region := (rows 255 255 4 8 255 0 255 255), good := (rows 211 211 215 219 211 211 211 211) }] }

theorem profile24_node31 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,96] 6 144 profile24_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,96] 6 144 profile24_node31_cert).mp (by decide +kernel))

def profile24_node32_cert : CutBound 8 := { lost := (rows 32 48 0 48 0 0 0 0), upper := (rows 19 194 37 200 48 48 64 128), lower := (rows 19 194 37 200 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 32 255 255), good := (rows 203 202 239 202 202 234 202 202) },{ target := 5, region := (rows 17 255 4 255 16 0 255 255), good := (rows 219 202 207 202 219 202 202 202) }] }

theorem profile24_node32 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,192] 6 48 profile24_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33,192] 6 48 profile24_node32_cert).mp (by decide +kernel))

def profile24_node28_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile24_node28_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node28 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,33] 6 (by decide) (choices 2) [48,80,96,192] profile24_node28_route profile24_node28_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile24_node29
  · exact profile24_node30
  · exact profile24_node31
  · exact profile24_node32

def profile24_node33_cert : CutBound 8 := { lost := (rows 32 48 0 16 0 0 0 0), upper := (rows 19 194 52 233 241 225 64 128), lower := (rows 19 194 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 9 0 33 255 255), good := (rows 235 194 230 202 194 226 194 194) },{ target := 5, region := (rows 21 255 4 8 16 0 255 255), good := (rows 211 194 215 202 211 194 194 194) }] }

theorem profile24_node33 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,48] 6 225 profile24_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,48] 6 225 profile24_node33_cert).mp (by decide +kernel))

def profile24_node34_cert : CutBound 8 := { lost := (rows 32 48 48 0 0 0 0 0), upper := (rows 19 194 69 184 176 176 64 128), lower := (rows 19 194 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 199 194 199 202 194 226 194 194) },{ target := 5, region := (rows 17 255 21 8 16 0 255 255), good := (rows 215 194 199 202 215 194 194 194) }] }

theorem profile24_node34 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,65] 6 176 profile24_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,65] 6 176 profile24_node34_cert).mp (by decide +kernel))

def profile24_node35_cert : CutBound 8 := { lost := (rows 32 48 32 16 0 0 0 0), upper := (rows 19 194 84 169 177 161 64 128), lower := (rows 19 194 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 9 0 33 255 255), good := (rows 235 194 198 202 194 226 194 194) },{ target := 5, region := (rows 21 255 21 8 16 0 255 255), good := (rows 215 194 215 202 215 194 194 194) }] }

theorem profile24_node35 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,80] 6 161 profile24_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,80] 6 161 profile24_node35_cert).mp (by decide +kernel))

def profile24_node36_cert : CutBound 8 := { lost := (rows 32 48 16 0 0 0 0 0), upper := (rows 19 194 100 185 177 177 64 128), lower := (rows 19 194 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 36 8 0 32 255 255), good := (rows 195 194 230 202 194 230 194 194) },{ target := 5, region := (rows 17 255 4 8 16 0 255 255), good := (rows 211 194 198 202 211 194 194 194) }] }

theorem profile24_node36 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,96] 6 177 profile24_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,96] 6 177 profile24_node36_cert).mp (by decide +kernel))

def profile24_node37_cert : CutBound 8 := { lost := (rows 32 48 48 0 0 0 0 0), upper := (rows 19 194 196 57 49 49 64 128), lower := (rows 19 194 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 255 8 0 32 255 255), good := (rows 199 198 198 206 198 230 198 198) },{ target := 5, region := (rows 17 255 255 8 16 0 255 255), good := (rows 215 198 198 206 215 198 198 198) }] }

theorem profile24_node37 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,192] 6 49 profile24_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192,192] 6 49 profile24_node37_cert).mp (by decide +kernel))

def profile24_node26_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node26_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node26 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18,192] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile24_node26_route profile24_node26_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node27
  · exact profile24_node28
  · exact profile24_node33
  · exact profile24_node34
  · exact profile24_node35
  · exact profile24_node36
  · exact profile24_node37

def profile24_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node1 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [18] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile24_node1_route profile24_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node2
  · exact profile24_node3
  · exact profile24_node12
  · exact profile24_node13
  · exact profile24_node14
  · exact profile24_node15
  · exact profile24_node26

def profile24_node39_cert : CutBound 8 := { lost := (rows 0 96 16 16 0 0 0 0), upper := (rows 49 19 230 234 242 226 64 128), lower := (rows 49 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 255 255), good := (rows 225 239 196 200 192 224 192 192) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 211 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 179 147 132 136 144 160 128 128) }] }

theorem profile24_node39 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,17] 6 226 profile24_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,17] 6 226 profile24_node39_cert).mp (by decide +kernel))

def profile24_node40_cert : CutBound 8 := { lost := (rows 192 192 0 0 0 0 0 0), upper := (rows 49 50 199 203 211 227 64 128), lower := (rows 49 50 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 3 3 4 8 16 32 0 255), good := (rows 179 179 132 136 144 160 128 128) },{ target := 7, region := (rows 3 3 4 8 16 32 255 0), good := (rows 115 115 68 72 80 96 64 64) }] }

theorem profile24_node40 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,48] 6 195 profile24_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,48] 6 195 profile24_node40_cert).mp (by decide +kernel))

def profile24_node42_cert : CutBound 8 := { lost := (rows 0 48 32 16 0 0 0 0), upper := (rows 49 67 22 232 240 224 64 128), lower := (rows 49 67 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 255 0 255 255 255), good := (rows 235 235 238 232 232 232 232 232) },{ target := 5, region := (rows 1 3 5 8 16 0 255 255), good := (rows 215 199 214 200 208 192 192 192) }] }

theorem profile24_node42 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,18] 6 224 profile24_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,18] 6 224 profile24_node42_cert).mp (by decide +kernel))

def profile24_node43_cert : CutBound 8 := { lost := (rows 0 48 0 48 0 0 0 0), upper := (rows 49 67 52 202 210 226 64 128), lower := (rows 49 67 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 228 200 192 224 192 192) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 212 200 208 192 192 192) }] }

theorem profile24_node43 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,48] 6 194 profile24_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,48] 6 194 profile24_node43_cert).mp (by decide +kernel))

def profile24_node44_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 49 67 70 184 176 176 64 128), lower := (rows 49 67 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 7 8 0 32 255 255), good := (rows 231 199 198 200 192 224 192 192) },{ target := 5, region := (rows 1 3 7 8 16 0 255 255), good := (rows 215 199 198 200 208 192 192 192) }] }

theorem profile24_node44 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,66] 6 176 profile24_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,66] 6 176 profile24_node44_cert).mp (by decide +kernel))

def profile24_node45_cert : CutBound 8 := { lost := (rows 0 48 32 16 0 0 0 0), upper := (rows 49 67 84 170 178 162 64 128), lower := (rows 49 67 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) },{ target := 5, region := (rows 1 3 21 8 16 0 255 255), good := (rows 215 199 212 200 212 192 192 192) }] }

theorem profile24_node45 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,80] 6 162 profile24_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,80] 6 162 profile24_node45_cert).mp (by decide +kernel))

def profile24_node46_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 49 67 134 248 240 240 64 128), lower := (rows 49 67 134 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 7 8 0 32 255 255), good := (rows 231 199 198 200 192 224 192 192) },{ target := 5, region := (rows 1 3 7 8 16 0 255 255), good := (rows 215 199 198 200 208 192 192 192) }] }

theorem profile24_node46 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,130] 6 240 profile24_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,130] 6 240 profile24_node46_cert).mp (by decide +kernel))

def profile24_node47_cert : CutBound 8 := { lost := (rows 0 48 32 16 0 0 0 0), upper := (rows 49 67 148 234 242 226 64 128), lower := (rows 49 67 148 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) },{ target := 5, region := (rows 1 3 21 8 16 0 255 255), good := (rows 215 199 212 200 212 192 192 192) }] }

theorem profile24_node47 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,144] 6 226 profile24_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,144] 6 226 profile24_node47_cert).mp (by decide +kernel))

def profile24_node48_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 49 67 196 186 178 178 64 128), lower := (rows 49 67 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 255 8 0 32 255 255), good := (rows 231 199 196 204 196 228 196 196) },{ target := 5, region := (rows 1 3 255 8 16 0 255 255), good := (rows 215 199 196 204 212 196 196 196) }] }

theorem profile24_node48 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,192] 6 178 profile24_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65,192] 6 178 profile24_node48_cert).mp (by decide +kernel))

def profile24_node41_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node41_route : Route 8 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile24_node41 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,65] 6 (by decide) (choices 2) [18,48,66,80,130,144,192] profile24_node41_route profile24_node41_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node42
  · exact profile24_node43
  · exact profile24_node44
  · exact profile24_node45
  · exact profile24_node46
  · exact profile24_node47
  · exact profile24_node48

def profile24_node50_cert : CutBound 8 := { lost := (rows 0 160 160 16 0 0 0 0), upper := (rows 49 82 7 232 240 224 64 128), lower := (rows 49 82 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 233 234 239 232 232 232 232 232) },{ target := 5, region := (rows 1 19 5 8 16 0 255 255), good := (rows 215 210 199 200 210 192 192 192) },{ target := 7, region := (rows 1 19 5 8 16 32 255 0), good := (rows 119 82 71 72 82 96 64 64) }] }

theorem profile24_node50 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,3] 6 224 profile24_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,3] 6 224 profile24_node50_cert).mp (by decide +kernel))

def profile24_node51_cert : CutBound 8 := { lost := (rows 0 32 16 48 0 0 0 0), upper := (rows 49 82 37 202 210 226 64 128), lower := (rows 49 82 37 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 255 255), good := (rows 229 234 229 200 192 224 192 192) },{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 223 218 218 218 218 218) }] }

theorem profile24_node51 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,33] 6 194 profile24_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,33] 6 194 profile24_node51_cert).mp (by decide +kernel))

def profile24_node52_cert : CutBound 8 := { lost := (rows 0 160 128 48 0 0 0 0), upper := (rows 49 82 38 201 209 225 64 128), lower := (rows 49 82 38 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 233 194 230 200 192 224 192 192) },{ target := 5, region := (rows 1 19 4 9 17 0 255 255), good := (rows 219 210 198 200 210 192 192 192) },{ target := 7, region := (rows 1 19 5 8 16 32 255 0), good := (rows 119 82 102 72 82 96 64 64) }] }

theorem profile24_node52 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,34] 6 193 profile24_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,34] 6 193 profile24_node52_cert).mp (by decide +kernel))

def profile24_node53_cert : CutBound 8 := { lost := (rows 0 32 48 16 0 0 0 0), upper := (rows 49 82 69 170 178 162 64 128), lower := (rows 49 82 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 255 255), good := (rows 229 234 197 200 192 224 192 192) },{ target := 5, region := (rows 1 19 5 8 16 0 255 255), good := (rows 215 210 199 200 210 192 192 192) }] }

theorem profile24_node53 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,65] 6 162 profile24_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,65] 6 162 profile24_node53_cert).mp (by decide +kernel))

def profile24_node54_cert : CutBound 8 := { lost := (rows 0 32 48 16 0 0 0 0), upper := (rows 49 82 70 169 177 161 64 128), lower := (rows 49 82 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 198 198 200 192 224 192 192) },{ target := 5, region := (rows 1 19 23 8 16 0 255 255), good := (rows 215 214 198 200 214 192 192 192) }] }

theorem profile24_node54 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,66] 6 161 profile24_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,66] 6 161 profile24_node54_cert).mp (by decide +kernel))

def profile24_node55_cert : CutBound 8 := { lost := (rows 64 32 16 96 0 0 0 0), upper := (rows 49 82 100 139 147 163 64 128), lower := (rows 49 82 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 37 8 0 32 255 255), good := (rows 229 194 228 200 192 228 192 192) },{ target := 5, region := (rows 1 19 4 9 17 0 255 255), good := (rows 219 210 196 200 210 192 192 192) },{ target := 6, region := (rows 3 2 4 10 18 34 0 255), good := (rows 177 187 164 136 144 160 128 128) }] }

theorem profile24_node55 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,96] 6 131 profile24_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,96] 6 131 profile24_node55_cert).mp (by decide +kernel))

def profile24_node56_cert : CutBound 8 := { lost := (rows 0 32 48 16 0 0 0 0), upper := (rows 49 82 133 234 242 226 64 128), lower := (rows 49 82 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 255 255), good := (rows 229 234 197 200 192 224 192 192) },{ target := 5, region := (rows 1 19 5 8 16 0 255 255), good := (rows 215 210 199 200 210 192 192 192) }] }

theorem profile24_node56 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,129] 6 226 profile24_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,129] 6 226 profile24_node56_cert).mp (by decide +kernel))

def profile24_node57_cert : CutBound 8 := { lost := (rows 0 32 48 16 0 0 0 0), upper := (rows 49 82 134 233 241 225 64 128), lower := (rows 49 82 134 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 198 198 200 192 224 192 192) },{ target := 5, region := (rows 1 19 23 8 16 0 255 255), good := (rows 215 214 198 200 214 192 192 192) }] }

theorem profile24_node57 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,130] 6 225 profile24_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,130] 6 225 profile24_node57_cert).mp (by decide +kernel))

def profile24_node58_cert : CutBound 8 := { lost := (rows 0 32 80 32 0 0 0 0), upper := (rows 49 82 164 203 211 227 64 128), lower := (rows 49 82 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 37 8 0 32 255 255), good := (rows 229 194 228 200 192 228 192 192) },{ target := 5, region := (rows 1 19 4 9 17 0 255 255), good := (rows 219 210 196 200 210 192 192 192) },{ target := 6, region := (rows 1 2 37 8 16 32 0 255), good := (rows 181 146 164 136 144 164 128 128) }] }

theorem profile24_node58 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,160] 6 195 profile24_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,160] 6 195 profile24_node58_cert).mp (by decide +kernel))

def profile24_node59_cert : CutBound 8 := { lost := (rows 64 32 48 64 0 0 0 0), upper := (rows 49 82 196 171 179 163 64 128), lower := (rows 49 82 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 229 198 196 204 196 228 196 196) },{ target := 5, region := (rows 1 19 255 8 16 0 255 255), good := (rows 215 214 196 204 214 196 196 196) },{ target := 6, region := (rows 3 2 4 10 18 34 0 255), good := (rows 177 187 132 136 144 160 128 128) }] }

theorem profile24_node59 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,192] 6 163 profile24_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80,192] 6 163 profile24_node59_cert).mp (by decide +kernel))

def profile24_node49_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile24_node49_route : Route 8 := (fun mask => (mask,id))

theorem profile24_node49 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,80] 6 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] profile24_node49_route profile24_node49_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node50
  · exact profile24_node51
  · exact profile24_node52
  · exact profile24_node53
  · exact profile24_node54
  · exact profile24_node55
  · exact profile24_node56
  · exact profile24_node57
  · exact profile24_node58
  · exact profile24_node59

def profile24_node61_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 49 194 7 248 240 240 64 128), lower := (rows 49 194 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 231 194 199 202 194 226 194 194) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 215 194 199 202 210 194 194 194) }] }

theorem profile24_node61 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,3] 6 240 profile24_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,3] 6 240 profile24_node61_cert).mp (by decide +kernel))

def profile24_node62_cert : CutBound 8 := { lost := (rows 0 48 32 16 0 0 0 0), upper := (rows 49 194 21 234 242 226 64 128), lower := (rows 49 194 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 239 234 234 234 234 234) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 215 194 215 202 210 194 194 194) }] }

theorem profile24_node62 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,17] 6 226 profile24_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,17] 6 226 profile24_node62_cert).mp (by decide +kernel))

def profile24_node63_cert : CutBound 8 := { lost := (rows 0 48 32 16 0 0 0 0), upper := (rows 49 194 22 233 241 225 64 128), lower := (rows 49 194 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 9 0 33 255 255), good := (rows 235 194 198 202 194 226 194 194) },{ target := 5, region := (rows 1 255 21 8 16 0 255 255), good := (rows 215 194 214 202 214 194 194 194) }] }

theorem profile24_node63 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,18] 6 225 profile24_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,18] 6 225 profile24_node63_cert).mp (by decide +kernel))

def profile24_node64_cert : CutBound 8 := { lost := (rows 0 48 0 48 0 0 0 0), upper := (rows 49 194 52 203 211 227 64 128), lower := (rows 49 194 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 9 0 33 255 255), good := (rows 235 194 230 202 194 226 194 194) },{ target := 5, region := (rows 1 255 4 9 17 0 255 255), good := (rows 219 194 214 202 210 194 194 194) }] }

theorem profile24_node64 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,48] 6 195 profile24_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,48] 6 195 profile24_node64_cert).mp (by decide +kernel))

def profile24_node65_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 49 194 69 186 178 178 64 128), lower := (rows 49 194 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 231 194 199 202 194 226 194 194) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 215 194 199 202 210 194 194 194) }] }

theorem profile24_node65 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,65] 6 178 profile24_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,65] 6 178 profile24_node65_cert).mp (by decide +kernel))

def profile24_node66_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 49 194 70 185 177 177 64 128), lower := (rows 49 194 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 255 8 0 32 255 255), good := (rows 231 198 198 206 198 230 198 198) },{ target := 5, region := (rows 1 255 255 8 16 0 255 255), good := (rows 215 198 198 206 214 198 198 198) }] }

theorem profile24_node66 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,66] 6 177 profile24_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,66] 6 177 profile24_node66_cert).mp (by decide +kernel))

def profile24_node67_cert : CutBound 8 := { lost := (rows 0 48 32 16 0 0 0 0), upper := (rows 49 194 84 171 179 163 64 128), lower := (rows 49 194 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 9 0 33 255 255), good := (rows 235 194 198 202 194 226 194 194) },{ target := 5, region := (rows 1 255 21 8 16 0 255 255), good := (rows 215 194 214 202 214 194 194 194) }] }

theorem profile24_node67 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,80] 6 163 profile24_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,80] 6 163 profile24_node67_cert).mp (by decide +kernel))

def profile24_node68_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 49 194 196 59 51 51 64 128), lower := (rows 49 194 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 255 8 0 32 255 255), good := (rows 231 198 198 206 198 230 198 198) },{ target := 5, region := (rows 1 255 255 8 16 0 255 255), good := (rows 215 198 198 206 214 198 198 198) }] }

theorem profile24_node68 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,192] 6 51 profile24_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192,192] 6 51 profile24_node68_cert).mp (by decide +kernel))

def profile24_node60_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node60_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node60 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48,192] 6 (by decide) (choices 2) [3,17,18,48,65,66,80,192] profile24_node60_route profile24_node60_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node61
  · exact profile24_node62
  · exact profile24_node63
  · exact profile24_node64
  · exact profile24_node65
  · exact profile24_node66
  · exact profile24_node67
  · exact profile24_node68

def profile24_node38_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node38_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node38 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [48] 6 (by decide) (choices 2) [17,48,65,80,192] profile24_node38_route profile24_node38_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile24_node39
  · exact profile24_node40
  · exact profile24_node41
  · exact profile24_node49
  · exact profile24_node60

def profile24_node70_cert : CutBound 8 := { lost := (rows 176 160 0 0 0 0 0 0), upper := (rows 67 19 244 248 240 240 64 128), lower := (rows 67 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 5, region := (rows 19 18 4 8 16 0 255 255), good := (rows 195 211 196 200 211 192 192 192) },{ target := 7, region := (rows 19 18 4 8 16 32 255 0), good := (rows 67 83 68 72 83 96 64 64) }] }

theorem profile24_node70 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,17] 6 240 profile24_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,17] 6 240 profile24_node70_cert).mp (by decide +kernel))

def profile24_node72_cert : CutBound 8 := { lost := (rows 48 0 32 16 0 0 0 0), upper := (rows 67 50 21 232 240 224 64 128), lower := (rows 67 50 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 255 0 255 255 255), good := (rows 235 235 237 232 232 232 232 232) },{ target := 5, region := (rows 3 2 6 8 16 0 255 255), good := (rows 199 215 213 200 208 192 192 192) }] }

theorem profile24_node72 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,17] 6 224 profile24_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,17] 6 224 profile24_node72_cert).mp (by decide +kernel))

def profile24_node73_cert : CutBound 8 := { lost := (rows 48 0 0 48 0 0 0 0), upper := (rows 67 50 52 201 209 225 64 128), lower := (rows 67 50 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 11 0 35 255 255), good := (rows 235 235 228 200 192 224 192 192) },{ target := 5, region := (rows 3 2 4 11 19 0 255 255), good := (rows 219 219 212 200 208 192 192 192) }] }

theorem profile24_node73 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,48] 6 193 profile24_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,48] 6 193 profile24_node73_cert).mp (by decide +kernel))

def profile24_node74_cert : CutBound 8 := { lost := (rows 48 0 48 0 0 0 0 0), upper := (rows 67 50 69 184 176 176 64 128), lower := (rows 67 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 255 255), good := (rows 199 231 197 200 192 224 192 192) },{ target := 5, region := (rows 3 2 7 8 16 0 255 255), good := (rows 199 215 197 200 208 192 192 192) }] }

theorem profile24_node74 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,65] 6 176 profile24_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,65] 6 176 profile24_node74_cert).mp (by decide +kernel))

def profile24_node75_cert : CutBound 8 := { lost := (rows 48 0 32 16 0 0 0 0), upper := (rows 67 50 84 169 177 161 64 128), lower := (rows 67 50 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) },{ target := 5, region := (rows 3 2 22 8 16 0 255 255), good := (rows 199 215 212 200 212 192 192 192) }] }

theorem profile24_node75 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,80] 6 161 profile24_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,80] 6 161 profile24_node75_cert).mp (by decide +kernel))

def profile24_node76_cert : CutBound 8 := { lost := (rows 48 0 48 0 0 0 0 0), upper := (rows 67 50 133 248 240 240 64 128), lower := (rows 67 50 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 255 255), good := (rows 199 231 197 200 192 224 192 192) },{ target := 5, region := (rows 3 2 7 8 16 0 255 255), good := (rows 199 215 197 200 208 192 192 192) }] }

theorem profile24_node76 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,129] 6 240 profile24_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,129] 6 240 profile24_node76_cert).mp (by decide +kernel))

def profile24_node77_cert : CutBound 8 := { lost := (rows 48 0 32 16 0 0 0 0), upper := (rows 67 50 148 233 241 225 64 128), lower := (rows 67 50 148 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) },{ target := 5, region := (rows 3 2 22 8 16 0 255 255), good := (rows 199 215 212 200 212 192 192 192) }] }

theorem profile24_node77 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,144] 6 225 profile24_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,144] 6 225 profile24_node77_cert).mp (by decide +kernel))

def profile24_node78_cert : CutBound 8 := { lost := (rows 48 0 48 0 0 0 0 0), upper := (rows 67 50 196 185 177 177 64 128), lower := (rows 67 50 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 255 8 0 32 255 255), good := (rows 199 231 196 204 196 228 196 196) },{ target := 5, region := (rows 3 2 255 8 16 0 255 255), good := (rows 199 215 196 204 212 196 196 196) }] }

theorem profile24_node78 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,192] 6 177 profile24_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48,192] 6 177 profile24_node78_cert).mp (by decide +kernel))

def profile24_node71_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node71_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile24_node71 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,48] 6 (by decide) (choices 2) [17,48,65,80,129,144,192] profile24_node71_route profile24_node71_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node72
  · exact profile24_node73
  · exact profile24_node74
  · exact profile24_node75
  · exact profile24_node76
  · exact profile24_node77
  · exact profile24_node78

def profile24_node79_cert : CutBound 8 := { lost := (rows 48 48 0 0 0 0 0 0), upper := (rows 67 67 180 184 176 176 64 128), lower := (rows 67 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 5, region := (rows 255 255 4 8 16 0 255 255), good := (rows 195 195 199 203 211 195 195 195) }] }

theorem profile24_node79 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,65] 6 176 profile24_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,65] 6 176 profile24_node79_cert).mp (by decide +kernel))

def profile24_node80_cert : CutBound 8 := { lost := (rows 48 32 64 64 0 0 0 0), upper := (rows 67 82 181 185 177 177 64 128), lower := (rows 67 82 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 5, region := (rows 19 18 4 8 16 0 255 255), good := (rows 195 211 196 200 211 192 192 192) },{ target := 6, region := (rows 1 2 5 9 17 33 0 255), good := (rows 191 146 132 136 144 160 128 128) }] }

theorem profile24_node80 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,80] 6 177 profile24_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,80] 6 177 profile24_node80_cert).mp (by decide +kernel))

def profile24_node81_cert : CutBound 8 := { lost := (rows 48 48 0 0 0 0 0 0), upper := (rows 67 131 244 248 240 240 64 128), lower := (rows 67 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 5, region := (rows 255 255 4 8 16 0 255 255), good := (rows 195 195 199 203 211 195 195 195) }] }

theorem profile24_node81 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,129] 6 240 profile24_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,129] 6 240 profile24_node81_cert).mp (by decide +kernel))

def profile24_node82_cert : CutBound 8 := { lost := (rows 48 96 0 0 0 0 0 0), upper := (rows 67 146 245 249 241 241 64 128), lower := (rows 67 146 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 5, region := (rows 19 18 4 8 16 0 255 255), good := (rows 195 211 196 200 211 192 192 192) },{ target := 6, region := (rows 1 18 4 8 16 32 0 255), good := (rows 131 146 132 136 146 160 128 128) }] }

theorem profile24_node82 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,144] 6 241 profile24_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,144] 6 241 profile24_node82_cert).mp (by decide +kernel))

def profile24_node83_cert : CutBound 8 := { lost := (rows 48 48 0 0 0 0 0 0), upper := (rows 67 194 181 185 177 177 64 128), lower := (rows 67 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 5, region := (rows 255 255 4 8 16 0 255 255), good := (rows 195 195 199 203 211 195 195 195) }] }

theorem profile24_node83 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,192] 6 177 profile24_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66,192] 6 177 profile24_node83_cert).mp (by decide +kernel))

def profile24_node69_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node69_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile24_node69 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [66] 6 (by decide) (choices 2) [17,48,65,80,129,144,192] profile24_node69_route profile24_node69_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node70
  · exact profile24_node71
  · exact profile24_node79
  · exact profile24_node80
  · exact profile24_node81
  · exact profile24_node82
  · exact profile24_node83

def profile24_node85_cert : CutBound 8 := { lost := (rows 32 32 16 16 0 0 0 0), upper := (rows 81 19 230 234 242 226 64 128), lower := (rows 81 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 255 255), good := (rows 193 239 196 200 192 224 192 192) },{ target := 5, region := (rows 19 19 4 8 16 0 255 255), good := (rows 211 211 196 200 211 192 192 192) }] }

theorem profile24_node85 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,17] 6 226 profile24_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,17] 6 226 profile24_node85_cert).mp (by decide +kernel))

def profile24_node87_cert : CutBound 8 := { lost := (rows 160 16 0 16 0 0 0 0), upper := (rows 81 35 22 232 240 224 64 128), lower := (rows 81 35 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 255 0 255 255 255), good := (rows 235 235 238 232 232 232 232 232) },{ target := 5, region := (rows 21 2 4 8 16 0 255 255), good := (rows 209 195 215 200 209 192 192 192) },{ target := 7, region := (rows 21 2 4 8 16 32 255 0), good := (rows 81 99 87 72 81 96 64 64) }] }

theorem profile24_node87 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,18] 6 224 profile24_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,18] 6 224 profile24_node87_cert).mp (by decide +kernel))

def profile24_node88_cert : CutBound 8 := { lost := (rows 32 0 80 32 0 0 0 0), upper := (rows 81 35 38 216 208 240 64 128), lower := (rows 81 35 38 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 193 231 230 200 192 224 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 223 217 217 217 217 217) },{ target := 6, region := (rows 1 2 6 8 16 32 0 255), good := (rows 145 167 166 136 144 160 128 128) }] }

theorem profile24_node88 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,34] 6 208 profile24_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,34] 6 208 profile24_node88_cert).mp (by decide +kernel))

def profile24_node89_cert : CutBound 8 := { lost := (rows 32 16 0 48 0 0 0 0), upper := (rows 81 35 52 202 210 226 64 128), lower := (rows 81 35 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 228 200 192 224 192 192) },{ target := 5, region := (rows 23 2 4 10 18 0 255 255), good := (rows 209 219 213 200 209 192 192 192) }] }

theorem profile24_node89 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,48] 6 194 profile24_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,48] 6 194 profile24_node89_cert).mp (by decide +kernel))

def profile24_node90_cert : CutBound 8 := { lost := (rows 32 64 48 64 0 0 0 0), upper := (rows 81 35 70 184 176 176 64 128), lower := (rows 81 35 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 193 231 198 200 192 224 192 192) },{ target := 5, region := (rows 17 2 6 8 16 0 255 255), good := (rows 209 199 198 200 209 192 192 192) },{ target := 6, region := (rows 1 3 4 255 255 255 0 255), good := (rows 187 187 190 184 184 184 184 184) }] }

theorem profile24_node90 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,66] 6 176 profile24_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,66] 6 176 profile24_node90_cert).mp (by decide +kernel))

def profile24_node91_cert : CutBound 8 := { lost := (rows 32 16 32 16 0 0 0 0), upper := (rows 81 35 84 170 178 162 64 128), lower := (rows 81 35 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) },{ target := 5, region := (rows 21 2 21 8 16 0 255 255), good := (rows 213 199 213 200 213 192 192 192) }] }

theorem profile24_node91 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,80] 6 162 profile24_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,80] 6 162 profile24_node91_cert).mp (by decide +kernel))

def profile24_node92_cert : CutBound 8 := { lost := (rows 32 64 16 96 0 0 0 0), upper := (rows 81 35 100 154 146 178 64 128), lower := (rows 81 35 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 255 255), good := (rows 193 231 228 200 192 228 192 192) },{ target := 5, region := (rows 19 2 4 10 18 0 255 255), good := (rows 209 219 196 200 209 192 192 192) },{ target := 6, region := (rows 1 3 4 11 19 35 0 255), good := (rows 187 187 164 136 144 160 128 128) }] }

theorem profile24_node92 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,96] 6 146 profile24_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,96] 6 146 profile24_node92_cert).mp (by decide +kernel))

def profile24_node93_cert : CutBound 8 := { lost := (rows 32 0 112 0 0 0 0 0), upper := (rows 81 35 134 248 240 240 64 128), lower := (rows 81 35 134 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 193 231 198 200 192 224 192 192) },{ target := 5, region := (rows 17 2 6 8 16 0 255 255), good := (rows 209 199 198 200 209 192 192 192) },{ target := 6, region := (rows 1 2 6 8 16 32 0 255), good := (rows 145 167 134 136 144 160 128 128) }] }

theorem profile24_node93 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,130] 6 240 profile24_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,130] 6 240 profile24_node93_cert).mp (by decide +kernel))

def profile24_node94_cert : CutBound 8 := { lost := (rows 32 16 32 16 0 0 0 0), upper := (rows 81 35 148 234 242 226 64 128), lower := (rows 81 35 148 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) },{ target := 5, region := (rows 21 2 21 8 16 0 255 255), good := (rows 213 199 213 200 213 192 192 192) }] }

theorem profile24_node94 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,144] 6 226 profile24_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,144] 6 226 profile24_node94_cert).mp (by decide +kernel))

def profile24_node95_cert : CutBound 8 := { lost := (rows 32 0 80 32 0 0 0 0), upper := (rows 81 35 164 218 210 242 64 128), lower := (rows 81 35 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 255 255), good := (rows 193 231 228 200 192 228 192 192) },{ target := 5, region := (rows 19 2 4 10 18 0 255 255), good := (rows 209 219 196 200 209 192 192 192) },{ target := 6, region := (rows 1 2 38 8 16 32 0 255), good := (rows 145 167 164 136 144 164 128 128) }] }

theorem profile24_node95 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,160] 6 210 profile24_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,160] 6 210 profile24_node95_cert).mp (by decide +kernel))

def profile24_node96_cert : CutBound 8 := { lost := (rows 32 64 48 64 0 0 0 0), upper := (rows 81 35 196 186 178 178 64 128), lower := (rows 81 35 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 231 196 204 196 228 196 196) },{ target := 5, region := (rows 17 2 255 8 16 0 255 255), good := (rows 213 199 196 204 213 196 196 196) },{ target := 6, region := (rows 1 3 4 11 19 35 0 255), good := (rows 187 187 132 136 144 160 128 128) }] }

theorem profile24_node96 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,192] 6 178 profile24_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33,192] 6 178 profile24_node96_cert).mp (by decide +kernel))

def profile24_node86_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node86_route : Route 8 := (fun mask => (mask,id))

theorem profile24_node86 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,33] 6 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192] profile24_node86_route profile24_node86_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node87
  · exact profile24_node88
  · exact profile24_node89
  · exact profile24_node90
  · exact profile24_node91
  · exact profile24_node92
  · exact profile24_node93
  · exact profile24_node94
  · exact profile24_node95
  · exact profile24_node96

def profile24_node98_cert : CutBound 8 := { lost := (rows 160 0 160 16 0 0 0 0), upper := (rows 81 50 7 232 240 224 64 128), lower := (rows 81 50 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 233 234 239 232 232 232 232 232) },{ target := 5, region := (rows 19 2 6 8 16 0 255 255), good := (rows 209 215 199 200 209 192 192 192) },{ target := 7, region := (rows 19 2 6 8 16 32 255 0), good := (rows 81 119 71 72 81 96 64 64) }] }

theorem profile24_node98 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,3] 6 224 profile24_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,3] 6 224 profile24_node98_cert).mp (by decide +kernel))

def profile24_node99_cert : CutBound 8 := { lost := (rows 160 0 128 48 0 0 0 0), upper := (rows 81 50 37 202 210 226 64 128), lower := (rows 81 50 37 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 255 255), good := (rows 193 234 229 200 192 224 192 192) },{ target := 5, region := (rows 19 2 4 10 18 0 255 255), good := (rows 209 219 197 200 209 192 192 192) },{ target := 7, region := (rows 19 2 6 8 16 32 255 0), good := (rows 81 119 101 72 81 96 64 64) }] }

theorem profile24_node99 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,33] 6 194 profile24_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,33] 6 194 profile24_node99_cert).mp (by decide +kernel))

def profile24_node100_cert : CutBound 8 := { lost := (rows 32 0 16 48 0 0 0 0), upper := (rows 81 50 38 201 209 225 64 128), lower := (rows 81 50 38 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 230 230 200 192 224 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 223 217 217 217 217 217) }] }

theorem profile24_node100 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,34] 6 193 profile24_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,34] 6 193 profile24_node100_cert).mp (by decide +kernel))

def profile24_node101_cert : CutBound 8 := { lost := (rows 32 0 48 16 0 0 0 0), upper := (rows 81 50 69 170 178 162 64 128), lower := (rows 81 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 255 255), good := (rows 197 234 197 200 192 224 192 192) },{ target := 5, region := (rows 19 2 23 8 16 0 255 255), good := (rows 213 215 197 200 213 192 192 192) }] }

theorem profile24_node101 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,65] 6 162 profile24_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,65] 6 162 profile24_node101_cert).mp (by decide +kernel))

def profile24_node102_cert : CutBound 8 := { lost := (rows 32 0 48 16 0 0 0 0), upper := (rows 81 50 70 169 177 161 64 128), lower := (rows 81 50 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 230 198 200 192 224 192 192) },{ target := 5, region := (rows 19 2 6 8 16 0 255 255), good := (rows 209 215 199 200 209 192 192 192) }] }

theorem profile24_node102 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,66] 6 161 profile24_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,66] 6 161 profile24_node102_cert).mp (by decide +kernel))

def profile24_node103_cert : CutBound 8 := { lost := (rows 32 64 16 96 0 0 0 0), upper := (rows 81 50 100 139 147 163 64 128), lower := (rows 81 50 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 255 255), good := (rows 193 230 228 200 192 228 192 192) },{ target := 5, region := (rows 19 2 4 10 18 0 255 255), good := (rows 209 219 196 200 209 192 192 192) },{ target := 6, region := (rows 1 3 4 9 17 33 0 255), good := (rows 187 178 164 136 144 160 128 128) }] }

theorem profile24_node103 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,96] 6 131 profile24_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,96] 6 131 profile24_node103_cert).mp (by decide +kernel))

def profile24_node104_cert : CutBound 8 := { lost := (rows 32 0 48 16 0 0 0 0), upper := (rows 81 50 133 234 242 226 64 128), lower := (rows 81 50 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 255 255), good := (rows 197 234 197 200 192 224 192 192) },{ target := 5, region := (rows 19 2 23 8 16 0 255 255), good := (rows 213 215 197 200 213 192 192 192) }] }

theorem profile24_node104 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,129] 6 226 profile24_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,129] 6 226 profile24_node104_cert).mp (by decide +kernel))

def profile24_node105_cert : CutBound 8 := { lost := (rows 32 0 48 16 0 0 0 0), upper := (rows 81 50 134 233 241 225 64 128), lower := (rows 81 50 134 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 230 198 200 192 224 192 192) },{ target := 5, region := (rows 19 2 6 8 16 0 255 255), good := (rows 209 215 199 200 209 192 192 192) }] }

theorem profile24_node105 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,130] 6 225 profile24_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,130] 6 225 profile24_node105_cert).mp (by decide +kernel))

def profile24_node106_cert : CutBound 8 := { lost := (rows 32 0 80 32 0 0 0 0), upper := (rows 81 50 164 203 211 227 64 128), lower := (rows 81 50 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 255 255), good := (rows 193 230 228 200 192 228 192 192) },{ target := 5, region := (rows 19 2 4 10 18 0 255 255), good := (rows 209 219 196 200 209 192 192 192) },{ target := 6, region := (rows 1 2 38 8 16 32 0 255), good := (rows 145 182 164 136 144 164 128 128) }] }

theorem profile24_node106 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,160] 6 195 profile24_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,160] 6 195 profile24_node106_cert).mp (by decide +kernel))

def profile24_node107_cert : CutBound 8 := { lost := (rows 32 64 48 64 0 0 0 0), upper := (rows 81 50 196 171 179 163 64 128), lower := (rows 81 50 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 230 196 204 196 228 196 196) },{ target := 5, region := (rows 19 2 255 8 16 0 255 255), good := (rows 213 215 196 204 213 196 196 196) },{ target := 6, region := (rows 1 3 4 9 17 33 0 255), good := (rows 187 178 132 136 144 160 128 128) }] }

theorem profile24_node107 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,192] 6 163 profile24_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48,192] 6 163 profile24_node107_cert).mp (by decide +kernel))

def profile24_node97_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile24_node97_route : Route 8 := (fun mask => (mask,id))

theorem profile24_node97 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,48] 6 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] profile24_node97_route profile24_node97_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node98
  · exact profile24_node99
  · exact profile24_node100
  · exact profile24_node101
  · exact profile24_node102
  · exact profile24_node103
  · exact profile24_node104
  · exact profile24_node105
  · exact profile24_node106
  · exact profile24_node107

def profile24_node108_cert : CutBound 8 := { lost := (rows 32 48 64 64 0 0 0 0), upper := (rows 81 67 182 186 178 178 64 128), lower := (rows 81 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 5, region := (rows 17 19 4 8 16 0 255 255), good := (rows 211 195 196 200 211 192 192 192) },{ target := 6, region := (rows 1 2 6 10 18 34 0 255), good := (rows 145 191 132 136 144 160 128 128) }] }

theorem profile24_node108 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,65] 6 178 profile24_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,65] 6 178 profile24_node108_cert).mp (by decide +kernel))

def profile24_node109_cert : CutBound 8 := { lost := (rows 160 160 0 0 0 0 0 0), upper := (rows 81 82 167 171 179 163 64 128), lower := (rows 81 82 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 19 19 4 8 16 0 255 255), good := (rows 211 211 196 200 211 192 192 192) },{ target := 7, region := (rows 19 19 4 8 16 32 255 0), good := (rows 83 83 68 72 83 96 64 64) }] }

theorem profile24_node109 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,80] 6 163 profile24_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,80] 6 163 profile24_node109_cert).mp (by decide +kernel))

def profile24_node110_cert : CutBound 8 := { lost := (rows 160 144 0 0 0 0 0 0), upper := (rows 81 98 183 187 179 179 64 128), lower := (rows 81 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) },{ target := 5, region := (rows 17 2 4 8 16 0 255 255), good := (rows 209 194 196 200 209 192 192 192) },{ target := 7, region := (rows 17 34 4 8 16 32 255 0), good := (rows 81 98 68 72 81 98 64 64) }] }

theorem profile24_node110 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,96] 6 179 profile24_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,96] 6 179 profile24_node110_cert).mp (by decide +kernel))

def profile24_node111_cert : CutBound 8 := { lost := (rows 32 112 0 0 0 0 0 0), upper := (rows 81 131 246 250 242 242 64 128), lower := (rows 81 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 5, region := (rows 17 19 4 8 16 0 255 255), good := (rows 211 195 196 200 211 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 147 131 132 136 144 160 128 128) }] }

theorem profile24_node111 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,129] 6 242 profile24_node111_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,129] 6 242 profile24_node111_cert).mp (by decide +kernel))

def profile24_node112_cert : CutBound 8 := { lost := (rows 160 96 0 0 0 0 0 0), upper := (rows 81 146 231 235 243 227 64 128), lower := (rows 81 146 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 19 19 4 8 16 0 255 255), good := (rows 211 211 196 200 211 192 192 192) },{ target := 6, region := (rows 1 19 4 8 16 32 0 255), good := (rows 147 146 132 136 146 160 128 128) },{ target := 7, region := (rows 19 2 4 8 16 32 255 0), good := (rows 81 83 68 72 81 96 64 64) }] }

theorem profile24_node112 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,144] 6 227 profile24_node112_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,144] 6 227 profile24_node112_cert).mp (by decide +kernel))

def profile24_node113_cert : CutBound 8 := { lost := (rows 160 80 0 0 0 0 0 0), upper := (rows 81 162 247 251 243 243 64 128), lower := (rows 81 162 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) },{ target := 5, region := (rows 17 2 4 8 16 0 255 255), good := (rows 209 194 196 200 209 192 192 192) },{ target := 6, region := (rows 1 34 4 8 16 32 0 255), good := (rows 145 162 132 136 144 162 128 128) },{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 98 68 72 81 96 64 64) }] }

theorem profile24_node113 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,160] 6 243 profile24_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,160] 6 243 profile24_node113_cert).mp (by decide +kernel))

def profile24_node114_cert : CutBound 8 := { lost := (rows 160 48 0 0 0 0 0 0), upper := (rows 81 194 183 187 179 179 64 128), lower := (rows 81 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 195 194 198 202 194 226 194 194) },{ target := 5, region := (rows 17 255 4 8 16 0 255 255), good := (rows 211 194 198 202 211 194 194 194) },{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 66 68 72 81 96 64 64) }] }

theorem profile24_node114 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,192] 6 179 profile24_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80,192] 6 179 profile24_node114_cert).mp (by decide +kernel))

def profile24_node84_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node84_route : Route 8 := (fun mask => (mask,id))

theorem profile24_node84 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [80] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile24_node84_route profile24_node84_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node85
  · exact profile24_node86
  · exact profile24_node97
  · exact profile24_node108
  · exact profile24_node109
  · exact profile24_node110
  · exact profile24_node111
  · exact profile24_node112
  · exact profile24_node113
  · exact profile24_node114

def profile24_node117_cert : CutBound 8 := { lost := (rows 48 32 32 16 0 0 0 0), upper := (rows 193 19 22 232 240 224 64 128), lower := (rows 193 19 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 239 233 233 233 233 233) },{ target := 5, region := (rows 255 22 22 8 16 0 255 255), good := (rows 193 215 215 201 215 193 193 193) }] }

theorem profile24_node117 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,18] 6 224 profile24_node117_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,18] 6 224 profile24_node117_cert).mp (by decide +kernel))

def profile24_node119_cert : CutBound 8 := { lost := (rows 48 32 16 0 0 0 0 0), upper := (rows 193 19 38 56 208 224 64 128), lower := (rows 193 19 38 56 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 255 255 255), good := (rows 225 231 231 233 225 225 225 225) },{ target := 5, region := (rows 255 255 4 8 255 0 255 255), good := (rows 211 211 215 219 211 211 211 211) }] }

theorem profile24_node119 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,48] 6 192 profile24_node119_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,48] 6 192 profile24_node119_cert).mp (by decide +kernel))

def profile24_node120_cert : CutBound 8 := { lost := (rows 48 32 16 32 0 0 0 0), upper := (rows 193 19 38 88 176 160 64 128), lower := (rows 193 19 38 88 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 255 255 255), good := (rows 225 231 231 233 225 225 225 225) },{ target := 5, region := (rows 255 26 4 26 16 0 255 255), good := (rows 193 219 207 219 219 193 193 193) }] }

theorem profile24_node120 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,80] 6 160 profile24_node120_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,80] 6 160 profile24_node120_cert).mp (by decide +kernel))

def profile24_node121_cert : CutBound 8 := { lost := (rows 48 32 0 16 0 0 0 0), upper := (rows 193 19 38 104 144 176 64 128), lower := (rows 193 19 38 104 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 44 0 32 255 255), good := (rows 193 195 239 233 193 233 193 193) },{ target := 5, region := (rows 255 255 4 8 255 0 255 255), good := (rows 211 211 215 219 211 211 211 211) }] }

theorem profile24_node121 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,96] 6 144 profile24_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,96] 6 144 profile24_node121_cert).mp (by decide +kernel))

def profile24_node122_cert : CutBound 8 := { lost := (rows 48 32 0 48 0 0 0 0), upper := (rows 193 19 38 200 48 48 64 128), lower := (rows 193 19 38 200 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 203 239 201 201 233 201 201) },{ target := 5, region := (rows 255 18 4 255 16 0 255 255), good := (rows 201 219 207 201 219 201 201 201) }] }

theorem profile24_node122 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,192] 6 48 profile24_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34,192] 6 48 profile24_node122_cert).mp (by decide +kernel))

def profile24_node118_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile24_node118_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node118 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,34] 6 (by decide) (choices 2) [48,80,96,192] profile24_node118_route profile24_node118_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile24_node119
  · exact profile24_node120
  · exact profile24_node121
  · exact profile24_node122

def profile24_node123_cert : CutBound 8 := { lost := (rows 48 32 0 16 0 0 0 0), upper := (rows 193 19 52 234 242 226 64 128), lower := (rows 193 19 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 34 255 255), good := (rows 193 235 229 201 193 225 193 193) },{ target := 5, region := (rows 255 22 4 8 16 0 255 255), good := (rows 193 211 215 201 211 193 193 193) }] }

theorem profile24_node123 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,48] 6 226 profile24_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,48] 6 226 profile24_node123_cert).mp (by decide +kernel))

def profile24_node124_cert : CutBound 8 := { lost := (rows 48 32 48 0 0 0 0 0), upper := (rows 193 19 70 184 176 176 64 128), lower := (rows 193 19 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 32 255 255), good := (rows 193 199 199 201 193 225 193 193) },{ target := 5, region := (rows 255 18 22 8 16 0 255 255), good := (rows 193 215 199 201 215 193 193 193) }] }

theorem profile24_node124 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,66] 6 176 profile24_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,66] 6 176 profile24_node124_cert).mp (by decide +kernel))

def profile24_node125_cert : CutBound 8 := { lost := (rows 48 32 32 16 0 0 0 0), upper := (rows 193 19 84 170 178 162 64 128), lower := (rows 193 19 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 34 255 255), good := (rows 193 235 197 201 193 225 193 193) },{ target := 5, region := (rows 255 22 22 8 16 0 255 255), good := (rows 193 215 215 201 215 193 193 193) }] }

theorem profile24_node125 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,80] 6 162 profile24_node125_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,80] 6 162 profile24_node125_cert).mp (by decide +kernel))

def profile24_node126_cert : CutBound 8 := { lost := (rows 48 32 16 0 0 0 0 0), upper := (rows 193 19 100 186 178 178 64 128), lower := (rows 193 19 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 195 229 201 193 229 193 193) },{ target := 5, region := (rows 255 18 4 8 16 0 255 255), good := (rows 193 211 197 201 211 193 193 193) }] }

theorem profile24_node126 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,96] 6 178 profile24_node126_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,96] 6 178 profile24_node126_cert).mp (by decide +kernel))

def profile24_node127_cert : CutBound 8 := { lost := (rows 48 32 48 0 0 0 0 0), upper := (rows 193 19 196 58 50 50 64 128), lower := (rows 193 19 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) },{ target := 5, region := (rows 255 18 255 8 16 0 255 255), good := (rows 197 215 197 205 215 197 197 197) }] }

theorem profile24_node127 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,192] 6 50 profile24_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17,192] 6 50 profile24_node127_cert).mp (by decide +kernel))

def profile24_node116_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node116_route : Route 8 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node116 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,17] 6 (by decide) (choices 2) [18,34,48,66,80,96,192] profile24_node116_route profile24_node116_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node117
  · exact profile24_node118
  · exact profile24_node123
  · exact profile24_node124
  · exact profile24_node125
  · exact profile24_node126
  · exact profile24_node127

def profile24_node129_cert : CutBound 8 := { lost := (rows 48 0 48 0 0 0 0 0), upper := (rows 193 50 7 248 240 240 64 128), lower := (rows 193 50 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 32 255 255), good := (rows 193 231 199 201 193 225 193 193) },{ target := 5, region := (rows 255 2 6 8 16 0 255 255), good := (rows 193 215 199 201 209 193 193 193) }] }

theorem profile24_node129 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,3] 6 240 profile24_node129_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,3] 6 240 profile24_node129_cert).mp (by decide +kernel))

def profile24_node130_cert : CutBound 8 := { lost := (rows 48 0 32 16 0 0 0 0), upper := (rows 193 50 21 234 242 226 64 128), lower := (rows 193 50 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 34 255 255), good := (rows 193 235 197 201 193 225 193 193) },{ target := 5, region := (rows 255 2 22 8 16 0 255 255), good := (rows 193 215 213 201 213 193 193 193) }] }

theorem profile24_node130 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,17] 6 226 profile24_node130_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,17] 6 226 profile24_node130_cert).mp (by decide +kernel))


#print axioms profile24_node130
end Delivery.SmallBudgetTenFinite8
