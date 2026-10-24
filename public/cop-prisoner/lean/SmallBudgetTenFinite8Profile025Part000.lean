import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile25_node2_cert : CutBound 8 := { lost := (rows 0 224 0 0 0 0 0 0), upper := (rows 49 19 244 248 240 240 64 128), lower := (rows 49 19 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 211 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 179 147 132 136 144 160 128 128) },{ target := 7, region := (rows 1 3 4 8 16 32 255 0), good := (rows 115 83 68 72 80 96 64 64) }] }

theorem profile25_node2 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,17] 6 240 profile25_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,17] 6 240 profile25_node2_cert).mp (by decide +kernel))

def profile25_node3_cert : CutBound 8 := { lost := (rows 0 16 32 32 0 0 0 0), upper := (rows 49 35 212 216 208 240 64 128), lower := (rows 49 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 227 227 196 200 192 224 192 192) },{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 221 223 220 220 220 220 220 220) }] }

theorem profile25_node3 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,33] 6 208 profile25_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,33] 6 208 profile25_node3_cert).mp (by decide +kernel))

def profile25_node4_cert : CutBound 8 := { lost := (rows 64 64 32 32 0 0 0 0), upper := (rows 49 50 213 217 209 241 64 128), lower := (rows 49 50 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 210 196 200 208 192 192 192) },{ target := 6, region := (rows 3 3 4 8 16 32 0 255), good := (rows 179 179 132 136 144 160 128 128) }] }

theorem profile25_node4 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,48] 6 209 profile25_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,48] 6 209 profile25_node4_cert).mp (by decide +kernel))

def profile25_node5_cert : CutBound 8 := { lost := (rows 0 176 0 0 0 0 0 0), upper := (rows 49 67 244 248 240 240 64 128), lower := (rows 49 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 227 195 196 200 192 224 192 192) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 195 196 200 208 192 192 192) },{ target := 7, region := (rows 1 3 4 8 16 32 255 0), good := (rows 115 67 68 72 80 96 64 64) }] }

theorem profile25_node5 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,65] 6 240 profile25_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,65] 6 240 profile25_node5_cert).mp (by decide +kernel))

def profile25_node7_cert : CutBound 8 := { lost := (rows 0 32 32 16 0 0 0 0), upper := (rows 49 82 21 232 240 224 64 128), lower := (rows 49 82 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 233 234 237 232 232 232 232 232) },{ target := 5, region := (rows 1 23 5 8 16 0 255 255), good := (rows 215 210 215 200 210 192 192 192) }] }

theorem profile25_node7 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,17] 6 224 profile25_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,17] 6 224 profile25_node7_cert).mp (by decide +kernel))

def profile25_node8_cert : CutBound 8 := { lost := (rows 0 32 16 32 0 0 0 0), upper := (rows 49 82 37 216 208 240 64 128), lower := (rows 49 82 37 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 229 194 229 200 192 224 192 192) },{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 223 218 218 218 218 218) }] }

theorem profile25_node8 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,33] 6 208 profile25_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,33] 6 208 profile25_node8_cert).mp (by decide +kernel))

def profile25_node9_cert : CutBound 8 := { lost := (rows 0 32 0 48 0 0 0 0), upper := (rows 49 82 52 201 209 225 64 128), lower := (rows 49 82 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 233 194 228 200 192 224 192 192) },{ target := 5, region := (rows 1 23 4 9 17 0 255 255), good := (rows 219 210 214 200 210 192 192 192) }] }

theorem profile25_node9 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,48] 6 193 profile25_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,48] 6 193 profile25_node9_cert).mp (by decide +kernel))

def profile25_node10_cert : CutBound 8 := { lost := (rows 0 32 48 0 0 0 0 0), upper := (rows 49 82 69 184 176 176 64 128), lower := (rows 49 82 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 229 194 197 200 192 224 192 192) },{ target := 5, region := (rows 1 19 5 8 16 0 255 255), good := (rows 215 210 199 200 210 192 192 192) }] }

theorem profile25_node10 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,65] 6 176 profile25_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,65] 6 176 profile25_node10_cert).mp (by decide +kernel))

def profile25_node11_cert : CutBound 8 := { lost := (rows 0 32 32 16 0 0 0 0), upper := (rows 49 82 84 169 177 161 64 128), lower := (rows 49 82 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 233 194 196 200 192 224 192 192) },{ target := 5, region := (rows 1 23 23 8 16 0 255 255), good := (rows 215 214 214 200 214 192 192 192) }] }

theorem profile25_node11 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,80] 6 161 profile25_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,80] 6 161 profile25_node11_cert).mp (by decide +kernel))

def profile25_node12_cert : CutBound 8 := { lost := (rows 0 32 16 32 0 0 0 0), upper := (rows 49 82 100 153 145 177 64 128), lower := (rows 49 82 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 37 8 0 32 255 255), good := (rows 229 194 228 200 192 228 192 192) },{ target := 5, region := (rows 1 19 4 9 17 0 255 255), good := (rows 219 210 196 200 210 192 192 192) }] }

theorem profile25_node12 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,96] 6 145 profile25_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,96] 6 145 profile25_node12_cert).mp (by decide +kernel))

def profile25_node13_cert : CutBound 8 := { lost := (rows 0 32 48 0 0 0 0 0), upper := (rows 49 82 133 248 240 240 64 128), lower := (rows 49 82 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 229 194 197 200 192 224 192 192) },{ target := 5, region := (rows 1 19 5 8 16 0 255 255), good := (rows 215 210 199 200 210 192 192 192) }] }

theorem profile25_node13 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,129] 6 240 profile25_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,129] 6 240 profile25_node13_cert).mp (by decide +kernel))

def profile25_node14_cert : CutBound 8 := { lost := (rows 0 32 32 16 0 0 0 0), upper := (rows 49 82 148 233 241 225 64 128), lower := (rows 49 82 148 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 233 194 196 200 192 224 192 192) },{ target := 5, region := (rows 1 23 23 8 16 0 255 255), good := (rows 215 214 214 200 214 192 192 192) }] }

theorem profile25_node14 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,144] 6 225 profile25_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,144] 6 225 profile25_node14_cert).mp (by decide +kernel))

def profile25_node15_cert : CutBound 8 := { lost := (rows 0 32 16 32 0 0 0 0), upper := (rows 49 82 164 217 209 241 64 128), lower := (rows 49 82 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 37 8 0 32 255 255), good := (rows 229 194 228 200 192 228 192 192) },{ target := 5, region := (rows 1 19 4 9 17 0 255 255), good := (rows 219 210 196 200 210 192 192 192) }] }

theorem profile25_node15 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,160] 6 209 profile25_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,160] 6 209 profile25_node15_cert).mp (by decide +kernel))

def profile25_node16_cert : CutBound 8 := { lost := (rows 0 32 48 0 0 0 0 0), upper := (rows 49 82 196 185 177 177 64 128), lower := (rows 49 82 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 229 198 196 204 196 228 196 196) },{ target := 5, region := (rows 1 19 255 8 16 0 255 255), good := (rows 215 214 196 204 214 196 196 196) }] }

theorem profile25_node16 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,192] 6 177 profile25_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80,192] 6 177 profile25_node16_cert).mp (by decide +kernel))

def profile25_node6_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile25_node6_route : Route 8 := (fun mask => (mask,id))

theorem profile25_node6 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,80] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile25_node6_route profile25_node6_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node7
  · exact profile25_node8
  · exact profile25_node9
  · exact profile25_node10
  · exact profile25_node11
  · exact profile25_node12
  · exact profile25_node13
  · exact profile25_node14
  · exact profile25_node15
  · exact profile25_node16

def profile25_node17_cert : CutBound 8 := { lost := (rows 0 16 32 32 0 0 0 0), upper := (rows 49 98 213 217 209 241 64 128), lower := (rows 49 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 35 4 8 0 32 255 255), good := (rows 227 226 196 200 192 226 192 192) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 194 196 200 208 192 192 192) }] }

theorem profile25_node17 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,96] 6 209 profile25_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,96] 6 209 profile25_node17_cert).mp (by decide +kernel))

def profile25_node19_cert : CutBound 8 := { lost := (rows 0 48 32 0 0 0 0 0), upper := (rows 49 194 21 248 240 240 64 128), lower := (rows 49 194 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 227 194 199 202 194 226 194 194) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 215 194 215 202 210 194 194 194) }] }

theorem profile25_node19 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,17] 6 240 profile25_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,17] 6 240 profile25_node19_cert).mp (by decide +kernel))

def profile25_node20_cert : CutBound 8 := { lost := (rows 0 48 16 32 0 0 0 0), upper := (rows 49 194 37 216 208 240 64 128), lower := (rows 49 194 37 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 231 194 231 202 194 226 194 194) },{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 223 218 218 218 218 218) }] }

theorem profile25_node20 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,33] 6 208 profile25_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,33] 6 208 profile25_node20_cert).mp (by decide +kernel))

def profile25_node21_cert : CutBound 8 := { lost := (rows 0 48 0 32 0 0 0 0), upper := (rows 49 194 52 217 209 241 64 128), lower := (rows 49 194 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 227 194 230 202 194 226 194 194) },{ target := 5, region := (rows 1 255 4 9 17 0 255 255), good := (rows 219 194 214 202 210 194 194 194) }] }

theorem profile25_node21 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,48] 6 209 profile25_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,48] 6 209 profile25_node21_cert).mp (by decide +kernel))

def profile25_node22_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 49 194 69 184 176 176 64 128), lower := (rows 49 194 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 231 194 199 202 194 226 194 194) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 215 194 199 202 210 194 194 194) }] }

theorem profile25_node22 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,65] 6 176 profile25_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,65] 6 176 profile25_node22_cert).mp (by decide +kernel))

def profile25_node23_cert : CutBound 8 := { lost := (rows 0 48 32 0 0 0 0 0), upper := (rows 49 194 84 185 177 177 64 128), lower := (rows 49 194 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 227 194 198 202 194 226 194 194) },{ target := 5, region := (rows 1 255 21 8 16 0 255 255), good := (rows 215 194 214 202 214 194 194 194) }] }

theorem profile25_node23 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,80] 6 177 profile25_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,80] 6 177 profile25_node23_cert).mp (by decide +kernel))

def profile25_node24_cert : CutBound 8 := { lost := (rows 0 48 16 32 0 0 0 0), upper := (rows 49 194 100 153 145 177 64 128), lower := (rows 49 194 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 37 8 0 32 255 255), good := (rows 231 194 230 202 194 230 194 194) },{ target := 5, region := (rows 1 255 4 9 17 0 255 255), good := (rows 219 194 198 202 210 194 194 194) }] }

theorem profile25_node24 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,96] 6 145 profile25_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,96] 6 145 profile25_node24_cert).mp (by decide +kernel))

def profile25_node25_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 49 194 196 57 49 49 64 128), lower := (rows 49 194 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 255 8 0 32 255 255), good := (rows 231 198 198 206 198 230 198 198) },{ target := 5, region := (rows 1 255 255 8 16 0 255 255), good := (rows 215 198 198 206 214 198 198 198) }] }

theorem profile25_node25 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,192] 6 49 profile25_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192,192] 6 49 profile25_node25_cert).mp (by decide +kernel))

def profile25_node18_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile25_node18_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile25_node18 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48,192] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile25_node18_route profile25_node18_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node19
  · exact profile25_node20
  · exact profile25_node21
  · exact profile25_node22
  · exact profile25_node23
  · exact profile25_node24
  · exact profile25_node25

def profile25_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile25_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile25_node1 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [48] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile25_node1_route profile25_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node2
  · exact profile25_node3
  · exact profile25_node4
  · exact profile25_node5
  · exact profile25_node6
  · exact profile25_node17
  · exact profile25_node18

def profile25_node27_cert : CutBound 8 := { lost := (rows 32 96 0 0 0 0 0 0), upper := (rows 81 19 244 248 240 240 64 128), lower := (rows 81 19 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 19 19 4 8 16 0 255 255), good := (rows 211 211 196 200 211 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 147 147 132 136 144 160 128 128) }] }

theorem profile25_node27 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,17] 6 240 profile25_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,17] 6 240 profile25_node27_cert).mp (by decide +kernel))

def profile25_node29_cert : CutBound 8 := { lost := (rows 160 128 0 32 0 0 0 0), upper := (rows 81 35 52 216 208 240 64 128), lower := (rows 81 35 52 8 16 32 64 128), losses := [{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) },{ target := 7, region := (rows 21 6 4 8 16 32 255 0), good := (rows 81 99 119 72 81 96 64 64) }] }

theorem profile25_node29 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,48] 6 208 profile25_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,48] 6 208 profile25_node29_cert).mp (by decide +kernel))

def profile25_node30_cert : CutBound 8 := { lost := (rows 32 64 32 64 0 0 0 0), upper := (rows 81 35 84 184 176 176 64 128), lower := (rows 81 35 84 8 16 32 64 128), losses := [{ target := 5, region := (rows 21 2 21 8 16 0 255 255), good := (rows 213 199 213 200 213 192 192 192) },{ target := 6, region := (rows 1 3 4 255 255 255 0 255), good := (rows 187 187 188 184 184 184 184 184) }] }

theorem profile25_node30 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,80] 6 176 profile25_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,80] 6 176 profile25_node30_cert).mp (by decide +kernel))

def profile25_node31_cert : CutBound 8 := { lost := (rows 32 0 16 32 0 0 0 0), upper := (rows 81 35 100 152 144 176 64 128), lower := (rows 81 35 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 255 255), good := (rows 193 231 228 200 192 228 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile25_node31 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,96] 6 144 profile25_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,96] 6 144 profile25_node31_cert).mp (by decide +kernel))

def profile25_node32_cert : CutBound 8 := { lost := (rows 32 0 96 0 0 0 0 0), upper := (rows 81 35 148 248 240 240 64 128), lower := (rows 81 35 148 8 16 32 64 128), losses := [{ target := 5, region := (rows 21 2 21 8 16 0 255 255), good := (rows 213 199 213 200 213 192 192 192) },{ target := 6, region := (rows 1 2 21 8 16 32 0 255), good := (rows 149 167 148 136 148 160 128 128) }] }

theorem profile25_node32 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,144] 6 240 profile25_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,144] 6 240 profile25_node32_cert).mp (by decide +kernel))

def profile25_node33_cert : CutBound 8 := { lost := (rows 32 0 16 32 0 0 0 0), upper := (rows 81 35 164 216 208 240 64 128), lower := (rows 81 35 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 255 255), good := (rows 193 231 228 200 192 228 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile25_node33 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,160] 6 208 profile25_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,160] 6 208 profile25_node33_cert).mp (by decide +kernel))

def profile25_node34_cert : CutBound 8 := { lost := (rows 32 0 48 0 0 0 0 0), upper := (rows 81 35 196 184 176 176 64 128), lower := (rows 81 35 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 231 196 204 196 228 196 196) },{ target := 5, region := (rows 17 2 255 8 16 0 255 255), good := (rows 213 199 196 204 213 196 196 196) }] }

theorem profile25_node34 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,192] 6 176 profile25_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33,192] 6 176 profile25_node34_cert).mp (by decide +kernel))

def profile25_node28_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile25_node28_route : Route 8 := (fun mask => (mask,id))

theorem profile25_node28 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,33] 6 (by decide) (choices 2) [48,80,96,144,160,192] profile25_node28_route profile25_node28_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node29
  · exact profile25_node30
  · exact profile25_node31
  · exact profile25_node32
  · exact profile25_node33
  · exact profile25_node34

def profile25_node36_cert : CutBound 8 := { lost := (rows 32 0 32 16 0 0 0 0), upper := (rows 81 50 21 232 240 224 64 128), lower := (rows 81 50 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 233 234 237 232 232 232 232 232) },{ target := 5, region := (rows 23 2 23 8 16 0 255 255), good := (rows 213 215 213 200 213 192 192 192) }] }

theorem profile25_node36 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,17] 6 224 profile25_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,17] 6 224 profile25_node36_cert).mp (by decide +kernel))

def profile25_node37_cert : CutBound 8 := { lost := (rows 160 0 128 32 0 0 0 0), upper := (rows 81 50 37 216 208 240 64 128), lower := (rows 81 50 37 8 16 32 64 128), losses := [{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) },{ target := 7, region := (rows 19 2 6 8 16 32 255 0), good := (rows 81 119 101 72 81 96 64 64) }] }

theorem profile25_node37 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,33] 6 208 profile25_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,33] 6 208 profile25_node37_cert).mp (by decide +kernel))

def profile25_node38_cert : CutBound 8 := { lost := (rows 32 0 0 48 0 0 0 0), upper := (rows 81 50 52 201 209 225 64 128), lower := (rows 81 50 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 233 226 228 200 192 224 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile25_node38 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,48] 6 193 profile25_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,48] 6 193 profile25_node38_cert).mp (by decide +kernel))

def profile25_node39_cert : CutBound 8 := { lost := (rows 32 0 48 0 0 0 0 0), upper := (rows 81 50 69 184 176 176 64 128), lower := (rows 81 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 197 226 197 200 192 224 192 192) },{ target := 5, region := (rows 19 2 23 8 16 0 255 255), good := (rows 213 215 197 200 213 192 192 192) }] }

theorem profile25_node39 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,65] 6 176 profile25_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,65] 6 176 profile25_node39_cert).mp (by decide +kernel))

def profile25_node40_cert : CutBound 8 := { lost := (rows 32 0 32 16 0 0 0 0), upper := (rows 81 50 84 169 177 161 64 128), lower := (rows 81 50 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 233 226 196 200 192 224 192 192) },{ target := 5, region := (rows 23 2 23 8 16 0 255 255), good := (rows 213 215 213 200 213 192 192 192) }] }

theorem profile25_node40 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,80] 6 161 profile25_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,80] 6 161 profile25_node40_cert).mp (by decide +kernel))

def profile25_node41_cert : CutBound 8 := { lost := (rows 32 0 16 32 0 0 0 0), upper := (rows 81 50 100 153 145 177 64 128), lower := (rows 81 50 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 255 255), good := (rows 193 230 228 200 192 228 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile25_node41 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,96] 6 145 profile25_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,96] 6 145 profile25_node41_cert).mp (by decide +kernel))

def profile25_node42_cert : CutBound 8 := { lost := (rows 32 0 48 0 0 0 0 0), upper := (rows 81 50 133 248 240 240 64 128), lower := (rows 81 50 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 197 226 197 200 192 224 192 192) },{ target := 5, region := (rows 19 2 23 8 16 0 255 255), good := (rows 213 215 197 200 213 192 192 192) }] }

theorem profile25_node42 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,129] 6 240 profile25_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,129] 6 240 profile25_node42_cert).mp (by decide +kernel))

def profile25_node43_cert : CutBound 8 := { lost := (rows 32 0 32 16 0 0 0 0), upper := (rows 81 50 148 233 241 225 64 128), lower := (rows 81 50 148 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 233 226 196 200 192 224 192 192) },{ target := 5, region := (rows 23 2 23 8 16 0 255 255), good := (rows 213 215 213 200 213 192 192 192) }] }

theorem profile25_node43 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,144] 6 225 profile25_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,144] 6 225 profile25_node43_cert).mp (by decide +kernel))

def profile25_node44_cert : CutBound 8 := { lost := (rows 32 0 16 32 0 0 0 0), upper := (rows 81 50 164 217 209 241 64 128), lower := (rows 81 50 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 255 255), good := (rows 193 230 228 200 192 228 192 192) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile25_node44 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,160] 6 209 profile25_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,160] 6 209 profile25_node44_cert).mp (by decide +kernel))

def profile25_node45_cert : CutBound 8 := { lost := (rows 32 0 48 0 0 0 0 0), upper := (rows 81 50 196 185 177 177 64 128), lower := (rows 81 50 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 230 196 204 196 228 196 196) },{ target := 5, region := (rows 19 2 255 8 16 0 255 255), good := (rows 213 215 196 204 213 196 196 196) }] }

theorem profile25_node45 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,192] 6 177 profile25_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48,192] 6 177 profile25_node45_cert).mp (by decide +kernel))

def profile25_node35_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile25_node35_route : Route 8 := (fun mask => (mask,id))

theorem profile25_node35 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,48] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile25_node35_route profile25_node35_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node36
  · exact profile25_node37
  · exact profile25_node38
  · exact profile25_node39
  · exact profile25_node40
  · exact profile25_node41
  · exact profile25_node42
  · exact profile25_node43
  · exact profile25_node44
  · exact profile25_node45

def profile25_node46_cert : CutBound 8 := { lost := (rows 32 48 0 0 0 0 0 0), upper := (rows 81 67 180 184 176 176 64 128), lower := (rows 81 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 5, region := (rows 17 19 4 8 16 0 255 255), good := (rows 211 195 196 200 211 192 192 192) }] }

theorem profile25_node46 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,65] 6 176 profile25_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,65] 6 176 profile25_node46_cert).mp (by decide +kernel))

def profile25_node47_cert : CutBound 8 := { lost := (rows 32 32 64 64 0 0 0 0), upper := (rows 81 82 181 185 177 177 64 128), lower := (rows 81 82 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 19 19 4 8 16 0 255 255), good := (rows 211 211 196 200 211 192 192 192) },{ target := 6, region := (rows 1 2 5 9 17 33 0 255), good := (rows 189 146 132 136 144 160 128 128) }] }

theorem profile25_node47 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,80] 6 177 profile25_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,80] 6 177 profile25_node47_cert).mp (by decide +kernel))

def profile25_node48_cert : CutBound 8 := { lost := (rows 32 16 64 64 0 0 0 0), upper := (rows 81 98 181 185 177 177 64 128), lower := (rows 81 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) },{ target := 5, region := (rows 17 2 4 8 16 0 255 255), good := (rows 209 194 196 200 209 192 192 192) },{ target := 6, region := (rows 1 2 5 9 17 33 0 255), good := (rows 189 162 132 136 144 160 128 128) }] }

theorem profile25_node48 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,96] 6 177 profile25_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,96] 6 177 profile25_node48_cert).mp (by decide +kernel))

def profile25_node49_cert : CutBound 8 := { lost := (rows 32 48 0 0 0 0 0 0), upper := (rows 81 131 244 248 240 240 64 128), lower := (rows 81 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 5, region := (rows 17 19 4 8 16 0 255 255), good := (rows 211 195 196 200 211 192 192 192) }] }

theorem profile25_node49 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,129] 6 240 profile25_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,129] 6 240 profile25_node49_cert).mp (by decide +kernel))

def profile25_node50_cert : CutBound 8 := { lost := (rows 32 96 0 0 0 0 0 0), upper := (rows 81 146 245 249 241 241 64 128), lower := (rows 81 146 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 19 19 4 8 16 0 255 255), good := (rows 211 211 196 200 211 192 192 192) },{ target := 6, region := (rows 1 19 4 8 16 32 0 255), good := (rows 147 146 132 136 146 160 128 128) }] }

theorem profile25_node50 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,144] 6 241 profile25_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,144] 6 241 profile25_node50_cert).mp (by decide +kernel))

def profile25_node51_cert : CutBound 8 := { lost := (rows 32 80 0 0 0 0 0 0), upper := (rows 81 162 245 249 241 241 64 128), lower := (rows 81 162 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) },{ target := 5, region := (rows 17 2 4 8 16 0 255 255), good := (rows 209 194 196 200 209 192 192 192) },{ target := 6, region := (rows 1 34 4 8 16 32 0 255), good := (rows 145 162 132 136 144 162 128 128) }] }

theorem profile25_node51 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,160] 6 241 profile25_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,160] 6 241 profile25_node51_cert).mp (by decide +kernel))

def profile25_node52_cert : CutBound 8 := { lost := (rows 32 48 0 0 0 0 0 0), upper := (rows 81 194 181 185 177 177 64 128), lower := (rows 81 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 195 194 198 202 194 226 194 194) },{ target := 5, region := (rows 17 255 4 8 16 0 255 255), good := (rows 211 194 198 202 211 194 194 194) }] }

theorem profile25_node52 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,192] 6 177 profile25_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80,192] 6 177 profile25_node52_cert).mp (by decide +kernel))

def profile25_node26_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile25_node26_route : Route 8 := (fun mask => (mask,id))

theorem profile25_node26 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [80] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile25_node26_route profile25_node26_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node27
  · exact profile25_node28
  · exact profile25_node35
  · exact profile25_node46
  · exact profile25_node47
  · exact profile25_node48
  · exact profile25_node49
  · exact profile25_node50
  · exact profile25_node51
  · exact profile25_node52

def profile25_node55_cert : CutBound 8 := { lost := (rows 16 32 0 32 0 0 0 0), upper := (rows 97 19 52 216 208 240 64 128), lower := (rows 97 19 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 37 2 4 8 0 32 255 255), good := (rows 225 195 229 200 192 225 192 192) },{ target := 5, region := (rows 1 3 4 255 255 0 255 255), good := (rows 219 219 220 216 216 216 216 216) }] }

theorem profile25_node55 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,48] 6 208 profile25_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,48] 6 208 profile25_node55_cert).mp (by decide +kernel))

def profile25_node56_cert : CutBound 8 := { lost := (rows 16 64 32 64 0 0 0 0), upper := (rows 97 19 84 184 176 176 64 128), lower := (rows 97 19 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 255 255), good := (rows 225 195 196 200 192 225 192 192) },{ target := 5, region := (rows 1 2 22 8 16 0 255 255), good := (rows 193 215 212 200 212 192 192 192) },{ target := 6, region := (rows 1 3 4 255 255 255 0 255), good := (rows 187 187 188 184 184 184 184 184) }] }

theorem profile25_node56 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,80] 6 176 profile25_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,80] 6 176 profile25_node56_cert).mp (by decide +kernel))

def profile25_node57_cert : CutBound 8 := { lost := (rows 16 32 16 32 0 0 0 0), upper := (rows 97 19 100 152 144 176 64 128), lower := (rows 97 19 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 37 2 37 8 0 32 255 255), good := (rows 229 199 229 200 192 229 192 192) },{ target := 5, region := (rows 1 3 4 255 255 0 255 255), good := (rows 219 219 220 216 216 216 216 216) }] }

theorem profile25_node57 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,96] 6 144 profile25_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,96] 6 144 profile25_node57_cert).mp (by decide +kernel))

def profile25_node58_cert : CutBound 8 := { lost := (rows 16 0 96 0 0 0 0 0), upper := (rows 97 19 148 248 240 240 64 128), lower := (rows 97 19 148 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 255 255), good := (rows 225 195 196 200 192 225 192 192) },{ target := 5, region := (rows 1 2 22 8 16 0 255 255), good := (rows 193 215 212 200 212 192 192 192) },{ target := 6, region := (rows 1 2 22 8 16 32 0 255), good := (rows 161 151 148 136 148 160 128 128) }] }

theorem profile25_node58 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,144] 6 240 profile25_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,144] 6 240 profile25_node58_cert).mp (by decide +kernel))

def profile25_node59_cert : CutBound 8 := { lost := (rows 16 32 16 32 0 0 0 0), upper := (rows 97 19 164 216 208 240 64 128), lower := (rows 97 19 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 37 2 37 8 0 32 255 255), good := (rows 229 199 229 200 192 229 192 192) },{ target := 5, region := (rows 1 3 4 255 255 0 255 255), good := (rows 219 219 220 216 216 216 216 216) }] }

theorem profile25_node59 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,160] 6 208 profile25_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,160] 6 208 profile25_node59_cert).mp (by decide +kernel))

def profile25_node60_cert : CutBound 8 := { lost := (rows 16 0 48 0 0 0 0 0), upper := (rows 97 19 196 184 176 176 64 128), lower := (rows 97 19 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 255 8 0 32 255 255), good := (rows 229 199 196 204 196 229 196 196) },{ target := 5, region := (rows 1 2 255 8 16 0 255 255), good := (rows 197 215 196 204 212 196 196 196) }] }

theorem profile25_node60 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,192] 6 176 profile25_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17,192] 6 176 profile25_node60_cert).mp (by decide +kernel))

def profile25_node54_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile25_node54_route : Route 8 := (fun mask => (mask,id))

theorem profile25_node54 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,17] 6 (by decide) (choices 2) [48,80,96,144,160,192] profile25_node54_route profile25_node54_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node55
  · exact profile25_node56
  · exact profile25_node57
  · exact profile25_node58
  · exact profile25_node59
  · exact profile25_node60

def profile25_node61_cert : CutBound 8 := { lost := (rows 16 16 32 32 0 0 0 0), upper := (rows 97 35 212 216 208 240 64 128), lower := (rows 97 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 35 35 4 8 0 32 255 255), good := (rows 227 227 196 200 192 227 192 192) },{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 221 223 220 220 220 220 220 220) }] }

theorem profile25_node61 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,33] 6 208 profile25_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,33] 6 208 profile25_node61_cert).mp (by decide +kernel))

def profile25_node62_cert : CutBound 8 := { lost := (rows 16 0 32 32 0 0 0 0), upper := (rows 97 50 213 217 209 241 64 128), lower := (rows 97 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 35 2 4 8 0 32 255 255), good := (rows 225 227 196 200 192 225 192 192) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 210 196 200 208 192 192 192) }] }

theorem profile25_node62 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,48] 6 209 profile25_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,48] 6 209 profile25_node62_cert).mp (by decide +kernel))

def profile25_node63_cert : CutBound 8 := { lost := (rows 16 48 0 0 0 0 0 0), upper := (rows 97 67 180 184 176 176 64 128), lower := (rows 97 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 255 255), good := (rows 227 195 196 200 192 227 192 192) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) }] }

theorem profile25_node63 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,65] 6 176 profile25_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,65] 6 176 profile25_node63_cert).mp (by decide +kernel))

def profile25_node64_cert : CutBound 8 := { lost := (rows 16 32 64 64 0 0 0 0), upper := (rows 97 82 181 185 177 177 64 128), lower := (rows 97 82 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 255 255), good := (rows 225 194 196 200 192 225 192 192) },{ target := 5, region := (rows 1 18 4 8 16 0 255 255), good := (rows 193 210 196 200 210 192 192 192) },{ target := 6, region := (rows 1 2 5 9 17 33 0 255), good := (rows 189 146 132 136 144 160 128 128) }] }

theorem profile25_node64 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,80] 6 177 profile25_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,80] 6 177 profile25_node64_cert).mp (by decide +kernel))

def profile25_node65_cert : CutBound 8 := { lost := (rows 16 16 32 32 0 0 0 0), upper := (rows 97 98 149 153 145 177 64 128), lower := (rows 97 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 35 35 4 8 0 32 255 255), good := (rows 227 227 196 200 192 227 192 192) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 194 196 200 208 192 192 192) }] }

theorem profile25_node65 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,96] 6 145 profile25_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,96] 6 145 profile25_node65_cert).mp (by decide +kernel))

def profile25_node66_cert : CutBound 8 := { lost := (rows 16 48 0 0 0 0 0 0), upper := (rows 97 131 244 248 240 240 64 128), lower := (rows 97 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 255 255), good := (rows 227 195 196 200 192 227 192 192) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) }] }

theorem profile25_node66 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,129] 6 240 profile25_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,129] 6 240 profile25_node66_cert).mp (by decide +kernel))

def profile25_node67_cert : CutBound 8 := { lost := (rows 16 96 0 0 0 0 0 0), upper := (rows 97 146 245 249 241 241 64 128), lower := (rows 97 146 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 255 255), good := (rows 225 194 196 200 192 225 192 192) },{ target := 5, region := (rows 1 18 4 8 16 0 255 255), good := (rows 193 210 196 200 210 192 192 192) },{ target := 6, region := (rows 1 18 4 8 16 32 0 255), good := (rows 161 146 132 136 146 160 128 128) }] }

theorem profile25_node67 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,144] 6 241 profile25_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,144] 6 241 profile25_node67_cert).mp (by decide +kernel))

def profile25_node68_cert : CutBound 8 := { lost := (rows 16 16 32 32 0 0 0 0), upper := (rows 97 162 213 217 209 241 64 128), lower := (rows 97 162 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 35 35 4 8 0 32 255 255), good := (rows 227 227 196 200 192 227 192 192) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 194 196 200 208 192 192 192) }] }

theorem profile25_node68 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,160] 6 209 profile25_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,160] 6 209 profile25_node68_cert).mp (by decide +kernel))

def profile25_node69_cert : CutBound 8 := { lost := (rows 16 48 0 0 0 0 0 0), upper := (rows 97 194 181 185 177 177 64 128), lower := (rows 97 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 255 4 8 0 32 255 255), good := (rows 227 194 198 202 194 227 194 194) },{ target := 5, region := (rows 1 255 4 8 16 0 255 255), good := (rows 195 194 198 202 210 194 194 194) }] }

theorem profile25_node69 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,192] 6 177 profile25_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96,192] 6 177 profile25_node69_cert).mp (by decide +kernel))

def profile25_node53_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile25_node53_route : Route 8 := (fun mask => (mask,id))

theorem profile25_node53 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [96] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile25_node53_route profile25_node53_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node54
  · exact profile25_node61
  · exact profile25_node62
  · exact profile25_node63
  · exact profile25_node64
  · exact profile25_node65
  · exact profile25_node66
  · exact profile25_node67
  · exact profile25_node68
  · exact profile25_node69

def profile25_node71_cert : CutBound 8 := { lost := (rows 48 32 0 0 0 0 0 0), upper := (rows 193 19 244 248 240 240 64 128), lower := (rows 193 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) },{ target := 5, region := (rows 255 18 4 8 16 0 255 255), good := (rows 193 211 197 201 211 193 193 193) }] }

theorem profile25_node71 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,17] 6 240 profile25_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,17] 6 240 profile25_node71_cert).mp (by decide +kernel))

def profile25_node72_cert : CutBound 8 := { lost := (rows 48 16 0 0 0 0 0 0), upper := (rows 193 35 244 248 240 240 64 128), lower := (rows 193 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 34 4 8 0 32 255 255), good := (rows 193 227 197 201 193 227 193 193) },{ target := 5, region := (rows 255 2 4 8 16 0 255 255), good := (rows 193 195 197 201 209 193 193 193) }] }

theorem profile25_node72 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,33] 6 240 profile25_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,33] 6 240 profile25_node72_cert).mp (by decide +kernel))

def profile25_node74_cert : CutBound 8 := { lost := (rows 48 0 32 0 0 0 0 0), upper := (rows 193 50 21 248 240 240 64 128), lower := (rows 193 50 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 227 197 201 193 225 193 193) },{ target := 5, region := (rows 255 2 22 8 16 0 255 255), good := (rows 193 215 213 201 213 193 193 193) }] }

theorem profile25_node74 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,17] 6 240 profile25_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,17] 6 240 profile25_node74_cert).mp (by decide +kernel))

def profile25_node75_cert : CutBound 8 := { lost := (rows 48 0 16 32 0 0 0 0), upper := (rows 193 50 37 216 208 240 64 128), lower := (rows 193 50 37 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 38 8 0 32 255 255), good := (rows 193 231 229 201 193 229 193 193) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile25_node75 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,33] 6 208 profile25_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,33] 6 208 profile25_node75_cert).mp (by decide +kernel))

def profile25_node76_cert : CutBound 8 := { lost := (rows 48 0 0 32 0 0 0 0), upper := (rows 193 50 52 217 209 241 64 128), lower := (rows 193 50 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 227 229 201 193 225 193 193) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile25_node76 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,48] 6 209 profile25_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,48] 6 209 profile25_node76_cert).mp (by decide +kernel))

def profile25_node77_cert : CutBound 8 := { lost := (rows 48 0 48 0 0 0 0 0), upper := (rows 193 50 69 184 176 176 64 128), lower := (rows 193 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) },{ target := 5, region := (rows 255 2 255 8 16 0 255 255), good := (rows 197 215 197 205 213 197 197 197) }] }

theorem profile25_node77 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,65] 6 176 profile25_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,65] 6 176 profile25_node77_cert).mp (by decide +kernel))

def profile25_node78_cert : CutBound 8 := { lost := (rows 48 0 32 0 0 0 0 0), upper := (rows 193 50 84 185 177 177 64 128), lower := (rows 193 50 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 227 197 201 193 225 193 193) },{ target := 5, region := (rows 255 2 22 8 16 0 255 255), good := (rows 193 215 213 201 213 193 193 193) }] }

theorem profile25_node78 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,80] 6 177 profile25_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,80] 6 177 profile25_node78_cert).mp (by decide +kernel))

def profile25_node79_cert : CutBound 8 := { lost := (rows 48 0 16 32 0 0 0 0), upper := (rows 193 50 100 153 145 177 64 128), lower := (rows 193 50 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 38 8 0 32 255 255), good := (rows 193 231 229 201 193 229 193 193) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile25_node79 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,96] 6 145 profile25_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,96] 6 145 profile25_node79_cert).mp (by decide +kernel))

def profile25_node80_cert : CutBound 8 := { lost := (rows 48 0 48 0 0 0 0 0), upper := (rows 193 50 196 57 49 49 64 128), lower := (rows 193 50 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) },{ target := 5, region := (rows 255 2 255 8 16 0 255 255), good := (rows 197 215 197 205 213 197 197 197) }] }

theorem profile25_node80 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,192] 6 49 profile25_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48,192] 6 49 profile25_node80_cert).mp (by decide +kernel))

def profile25_node73_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile25_node73_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile25_node73 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,48] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile25_node73_route profile25_node73_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node74
  · exact profile25_node75
  · exact profile25_node76
  · exact profile25_node77
  · exact profile25_node78
  · exact profile25_node79
  · exact profile25_node80

def profile25_node81_cert : CutBound 8 := { lost := (rows 48 48 0 0 0 0 0 0), upper := (rows 193 67 180 184 176 176 64 128), lower := (rows 193 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 5, region := (rows 255 255 4 8 16 0 255 255), good := (rows 195 195 199 203 211 195 195 195) }] }

theorem profile25_node81 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,65] 6 176 profile25_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,65] 6 176 profile25_node81_cert).mp (by decide +kernel))

def profile25_node82_cert : CutBound 8 := { lost := (rows 48 32 0 0 0 0 0 0), upper := (rows 193 82 181 185 177 177 64 128), lower := (rows 193 82 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) },{ target := 5, region := (rows 255 18 4 8 16 0 255 255), good := (rows 193 211 197 201 211 193 193 193) }] }

theorem profile25_node82 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,80] 6 177 profile25_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,80] 6 177 profile25_node82_cert).mp (by decide +kernel))

def profile25_node83_cert : CutBound 8 := { lost := (rows 48 16 0 0 0 0 0 0), upper := (rows 193 98 181 185 177 177 64 128), lower := (rows 193 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 34 4 8 0 32 255 255), good := (rows 193 227 197 201 193 227 193 193) },{ target := 5, region := (rows 255 2 4 8 16 0 255 255), good := (rows 193 195 197 201 209 193 193 193) }] }

theorem profile25_node83 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,96] 6 177 profile25_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,96] 6 177 profile25_node83_cert).mp (by decide +kernel))

def profile25_node84_cert : CutBound 8 := { lost := (rows 48 48 0 0 0 0 0 0), upper := (rows 193 194 53 57 49 49 64 128), lower := (rows 193 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 5, region := (rows 255 255 4 8 16 0 255 255), good := (rows 195 195 199 203 211 195 195 195) }] }

theorem profile25_node84 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,192] 6 49 profile25_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192,192] 6 49 profile25_node84_cert).mp (by decide +kernel))

def profile25_node70_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile25_node70_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile25_node70 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [192] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile25_node70_route profile25_node70_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node71
  · exact profile25_node72
  · exact profile25_node73
  · exact profile25_node81
  · exact profile25_node82
  · exact profile25_node83
  · exact profile25_node84

def profile25_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile25_node0_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile25_node0 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [] 6 (by decide) (choices 2) [48,80,96,192] profile25_node0_route profile25_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile25_node1
  · exact profile25_node26
  · exact profile25_node53
  · exact profile25_node70

theorem profile25 : Upper (D (n:=8) [33,32,32,32,19,18,2,2]) (R (n:=8) [33,32,32,32,19,18,2,2]) [] 6 := profile25_node0


#print axioms profile25
end Delivery.SmallBudgetTenFinite8
