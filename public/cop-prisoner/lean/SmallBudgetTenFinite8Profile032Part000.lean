import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile32_node2_cert : CutBound 8 := { lost := (rows 32 32 24 0 0 0 0 0), upper := (rows 25 26 228 232 240 224 224 128), lower := (rows 25 26 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) },{ target := 5, region := (rows 3 3 4 8 16 0 64 255), good := (rows 155 155 132 136 144 128 192 128) }] }

theorem profile32_node2 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,24] 6 224 profile32_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,24] 6 224 profile32_node2_cert).mp (by decide +kernel))

def profile32_node4_cert : CutBound 8 := { lost := (rows 32 16 8 0 0 0 0 0), upper := (rows 25 42 52 200 208 224 192 128), lower := (rows 25 42 52 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile32_node4 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,48] 6 192 profile32_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,48] 6 192 profile32_node4_cert).mp (by decide +kernel))

def profile32_node6_cert : CutBound 8 := { lost := (rows 32 16 40 0 0 0 0 0), upper := (rows 25 42 84 40 208 224 192 128), lower := (rows 25 42 84 40 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) },{ target := 5, region := (rows 11 2 255 8 255 0 255 255), good := (rows 221 223 212 221 212 212 212 212) }] }

theorem profile32_node6 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,80,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,80,32] 6 192 profile32_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,80,32] 6 192 profile32_node6_cert).mp (by decide +kernel))

def profile32_node7_cert : CutBound 8 := { lost := (rows 32 16 8 0 0 0 0 0), upper := (rows 25 42 84 72 176 160 224 128), lower := (rows 25 42 84 72 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) },{ target := 5, region := (rows 5 2 4 76 16 0 64 255), good := (rows 153 138 221 200 144 128 200 128) }] }

theorem profile32_node7 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,80,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,80,64] 6 160 profile32_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,80,64] 6 160 profile32_node7_cert).mp (by decide +kernel))

def profile32_node8_cert : CutBound 8 := { lost := (rows 32 16 8 0 0 0 0 0), upper := (rows 25 42 84 136 240 224 224 128), lower := (rows 25 42 84 136 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) },{ target := 5, region := (rows 21 2 4 255 16 0 64 255), good := (rows 153 138 221 136 153 136 200 136) }] }

theorem profile32_node8 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,80,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,80,128] 6 224 profile32_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,80,128] 6 224 profile32_node8_cert).mp (by decide +kernel))

def profile32_node5_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0

def profile32_node5_route : Route 8 := (fun mask => (mask,id))

theorem profile32_node5 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,80] 6 (by decide) (choices 1) [32,64,128] profile32_node5_route profile32_node5_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile32_node6
  · exact profile32_node7
  · exact profile32_node8

def profile32_node10_cert : CutBound 8 := { lost := (rows 0 16 24 0 0 0 0 0), upper := (rows 25 42 100 24 208 224 192 128), lower := (rows 25 42 100 24 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 11 255 8 0 255 255 255), good := (rows 239 238 228 238 228 228 228 228) }] }

theorem profile32_node10 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,96,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,96,16] 6 192 profile32_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,96,16] 6 192 profile32_node10_cert).mp (by decide +kernel))

def profile32_node11_cert : CutBound 8 := { lost := (rows 32 16 8 0 0 0 0 0), upper := (rows 25 42 100 72 144 176 208 128), lower := (rows 25 42 100 72 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 6 4 76 0 32 64 255), good := (rows 137 170 238 200 128 160 200 128) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile32_node11 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,96,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,96,64] 6 144 profile32_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,96,64] 6 144 profile32_node11_cert).mp (by decide +kernel))

def profile32_node12_cert : CutBound 8 := { lost := (rows 32 16 8 0 0 0 0 0), upper := (rows 25 42 100 136 208 240 208 128), lower := (rows 25 42 100 136 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 38 4 255 0 32 64 255), good := (rows 137 170 238 136 136 170 200 136) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile32_node12 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,96,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,96,128] 6 208 profile32_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,96,128] 6 208 profile32_node12_cert).mp (by decide +kernel))

def profile32_node9_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0

def profile32_node9_route : Route 8 := (fun mask => (mask,id))

theorem profile32_node9 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,96] 6 (by decide) (choices 1) [16,64,128] profile32_node9_route profile32_node9_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile32_node10
  · exact profile32_node11
  · exact profile32_node12

def profile32_node13_cert : CutBound 8 := { lost := (rows 0 16 40 0 0 0 0 0), upper := (rows 25 42 148 232 240 224 224 128), lower := (rows 25 42 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) },{ target := 5, region := (rows 1 2 21 8 16 0 64 255), good := (rows 157 138 148 136 148 128 192 128) }] }

theorem profile32_node13 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,144] 6 224 profile32_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,144] 6 224 profile32_node13_cert).mp (by decide +kernel))

def profile32_node14_cert : CutBound 8 := { lost := (rows 32 0 24 0 0 0 0 0), upper := (rows 25 42 164 216 208 240 208 128), lower := (rows 25 42 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 2 38 8 0 32 64 255), good := (rows 137 174 164 136 128 164 192 128) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile32_node14 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,160] 6 208 profile32_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,160] 6 208 profile32_node14_cert).mp (by decide +kernel))

def profile32_node15_cert : CutBound 8 := { lost := (rows 0 0 56 0 0 0 0 0), upper := (rows 25 42 196 248 240 240 240 128), lower := (rows 25 42 196 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 2 68 8 0 32 64 255), good := (rows 137 170 196 136 128 160 196 128) },{ target := 5, region := (rows 1 2 68 8 16 0 64 255), good := (rows 153 138 196 136 144 128 196 128) }] }

theorem profile32_node15 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,192] 6 240 profile32_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40,192] 6 240 profile32_node15_cert).mp (by decide +kernel))

def profile32_node3_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile32_node3_route : Route 8 := (fun mask => (mask,id))

theorem profile32_node3 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,40] 6 (by decide) (choices 2) [48,80,96,144,160,192] profile32_node3_route profile32_node3_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node4
  · exact profile32_node5
  · exact profile32_node9
  · exact profile32_node13
  · exact profile32_node14
  · exact profile32_node15

def profile32_node17_cert : CutBound 8 := { lost := (rows 32 24 32 0 0 0 0 0), upper := (rows 25 98 28 232 240 224 224 128), lower := (rows 25 98 28 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 255 4 0 255 255 255 255), good := (rows 243 242 246 242 242 242 242 242) },{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) },{ target := 5, region := (rows 5 2 5 8 16 0 64 255), good := (rows 157 194 157 136 144 128 192 128) }] }

theorem profile32_node17 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,24] 6 224 profile32_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,24] 6 224 profile32_node17_cert).mp (by decide +kernel))

def profile32_node19_cert : CutBound 8 := { lost := (rows 0 24 16 0 0 0 0 0), upper := (rows 25 98 44 24 208 224 192 128), lower := (rows 25 98 44 24 16 32 64 128), losses := [{ target := 3, region := (rows 1 255 4 0 255 255 255 255), good := (rows 243 242 246 242 242 242 242 242) },{ target := 4, region := (rows 1 255 13 8 0 255 255 255), good := (rows 239 226 238 238 226 226 226 226) }] }

theorem profile32_node19 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,40,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,40,16] 6 192 profile32_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,40,16] 6 192 profile32_node19_cert).mp (by decide +kernel))

def profile32_node20_cert : CutBound 8 := { lost := (rows 32 8 16 0 0 0 0 0), upper := (rows 25 98 44 72 144 176 208 128), lower := (rows 25 98 44 72 16 32 64 128), losses := [{ target := 3, region := (rows 1 255 4 0 255 255 255 255), good := (rows 243 242 246 242 242 242 242 242) },{ target := 4, region := (rows 1 2 6 74 0 32 64 255), good := (rows 137 238 172 200 128 160 200 128) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile32_node20 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,40,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,40,64] 6 144 profile32_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,40,64] 6 144 profile32_node20_cert).mp (by decide +kernel))

def profile32_node21_cert : CutBound 8 := { lost := (rows 32 8 16 0 0 0 0 0), upper := (rows 25 98 44 136 208 240 208 128), lower := (rows 25 98 44 136 16 32 64 128), losses := [{ target := 3, region := (rows 1 255 4 0 255 255 255 255), good := (rows 243 242 246 242 242 242 242 242) },{ target := 4, region := (rows 1 2 38 255 0 32 64 255), good := (rows 137 238 172 136 136 172 200 136) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile32_node21 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,40,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,40,128] 6 208 profile32_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,40,128] 6 208 profile32_node21_cert).mp (by decide +kernel))

def profile32_node18_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0

def profile32_node18_route : Route 8 := (fun mask => (mask,id))

theorem profile32_node18 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,40] 6 (by decide) (choices 1) [16,64,128] profile32_node18_route profile32_node18_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile32_node19
  · exact profile32_node20
  · exact profile32_node21

def profile32_node22_cert : CutBound 8 := { lost := (rows 0 24 24 0 0 0 0 0), upper := (rows 25 98 100 152 152 184 216 128), lower := (rows 25 98 100 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 6 6 0 16 32 64 255), good := (rows 145 230 230 128 144 160 192 128) },{ target := 4, region := (rows 1 6 6 8 0 32 64 255), good := (rows 137 230 230 136 128 160 192 128) }] }

theorem profile32_node22 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,96] 6 152 profile32_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,96] 6 152 profile32_node22_cert).mp (by decide +kernel))

def profile32_node23_cert : CutBound 8 := { lost := (rows 0 8 48 0 0 0 0 0), upper := (rows 25 98 140 248 240 240 240 128), lower := (rows 25 98 140 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 255 4 0 255 255 255 255), good := (rows 243 242 246 242 242 242 242 242) },{ target := 4, region := (rows 1 2 13 8 0 32 64 255), good := (rows 141 226 140 140 128 160 192 128) },{ target := 5, region := (rows 1 2 13 8 16 0 64 255), good := (rows 157 194 140 140 144 128 192 128) }] }

theorem profile32_node23 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,136] 6 240 profile32_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,136] 6 240 profile32_node23_cert).mp (by decide +kernel))

def profile32_node24_cert : CutBound 8 := { lost := (rows 32 0 24 0 0 0 0 0), upper := (rows 25 98 164 216 216 248 216 128), lower := (rows 25 98 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 38 0 16 32 64 255), good := (rows 145 230 164 128 144 164 192 128) },{ target := 4, region := (rows 1 2 38 8 0 32 64 255), good := (rows 137 230 164 136 128 164 192 128) },{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile32_node24 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,160] 6 216 profile32_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96,160] 6 216 profile32_node24_cert).mp (by decide +kernel))

def profile32_node16_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | _ => 0

def profile32_node16_route : Route 8 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile32_node16 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,96] 6 (by decide) (choices 2) [24,40,96,136,160] profile32_node16_route profile32_node16_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile32_node17
  · exact profile32_node18
  · exact profile32_node22
  · exact profile32_node23
  · exact profile32_node24

def profile32_node25_cert : CutBound 8 := { lost := (rows 0 48 8 0 0 0 0 0), upper := (rows 25 138 244 248 240 240 240 128), lower := (rows 25 138 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 246 244 244 244 244 244 244) },{ target := 4, region := (rows 1 11 4 8 0 32 64 255), good := (rows 139 138 132 138 128 160 192 128) },{ target := 5, region := (rows 1 11 4 8 16 0 64 255), good := (rows 155 138 132 138 144 128 192 128) }] }

theorem profile32_node25 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,136] 6 240 profile32_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,136] 6 240 profile32_node25_cert).mp (by decide +kernel))

def profile32_node26_cert : CutBound 8 := { lost := (rows 0 88 0 0 0 0 0 0), upper := (rows 25 162 252 248 248 248 248 128), lower := (rows 25 162 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 64 255), good := (rows 145 162 132 128 144 162 192 128) },{ target := 4, region := (rows 1 34 4 8 0 32 64 255), good := (rows 137 162 132 136 128 162 192 128) },{ target := 6, region := (rows 1 34 4 8 16 32 0 255), good := (rows 153 162 132 136 144 162 128 128) }] }

theorem profile32_node26 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,160] 6 248 profile32_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24,160] 6 248 profile32_node26_cert).mp (by decide +kernel))

def profile32_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile32_node1_route : Route 8 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile32_node1 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [24] 6 (by decide) (choices 2) [24,40,96,136,160] profile32_node1_route profile32_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile32_node2
  · exact profile32_node3
  · exact profile32_node16
  · exact profile32_node25
  · exact profile32_node26

def profile32_node27_cert : CutBound 8 := { lost := (rows 112 0 0 0 0 0 0 0), upper := (rows 137 250 252 248 248 248 248 128), lower := (rows 137 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 9 2 4 8 0 32 64 255), good := (rows 137 130 132 137 128 160 192 128) },{ target := 5, region := (rows 9 2 4 8 16 0 64 255), good := (rows 137 130 132 137 144 128 192 128) },{ target := 6, region := (rows 9 2 4 8 16 32 0 255), good := (rows 137 130 132 137 144 160 128 128) }] }

theorem profile32_node27 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [136] 6 248 profile32_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [136] 6 248 profile32_node27_cert).mp (by decide +kernel))

def profile32_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile32_node0_route : Route 8 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 80 => (24,(fun i => match i.val with | 3 => 6 | 6 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 96 => (24,(fun i => match i.val with | 3 => 5 | 4 => 6 | 5 => 3 | 6 => 4 | _ => i)) | 160 => (136,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 192 => (136,(fun i => match i.val with | 3 => 6 | 6 => 3 | _ => i)) | _ => (mask,id))

theorem profile32_node0 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [] 6 (by decide) (choices 2) [24,136] profile32_node0_route profile32_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile32_node1
  · exact profile32_node27

theorem profile32 : Upper (D (n:=8) [32,32,32,18,18,18,18,2]) (R (n:=8) [32,32,32,18,18,18,18,2]) [] 6 := profile32_node0


#print axioms profile32
end Delivery.SmallBudgetTenFinite8
