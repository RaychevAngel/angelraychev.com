import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile30_node2_cert : CutBound 8 := { lost := (rows 0 16 8 0 0 0 0 0), upper := (rows 25 11 244 248 240 240 240 128), lower := (rows 25 11 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 247 244 244 244 244 244 244) },{ target := 4, region := (rows 1 3 4 8 0 32 64 255), good := (rows 139 139 132 136 128 160 192 128) }] }

theorem profile30_node2 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,9] 6 240 profile30_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,9] 6 240 profile30_node2_cert).mp (by decide +kernel))

def profile30_node3_cert : CutBound 8 := { lost := (rows 0 0 24 0 0 0 0 0), upper := (rows 25 26 229 233 241 225 225 128), lower := (rows 25 26 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 255), good := (rows 245 146 132 128 144 160 192 128) },{ target := 4, region := (rows 1 2 5 9 0 33 65 255), good := (rows 237 138 132 136 128 160 192 128) }] }

theorem profile30_node3 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,24] 6 225 profile30_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,24] 6 225 profile30_node3_cert).mp (by decide +kernel))

def profile30_node5_cert : Bound 8 := { allowed := (rows 160 144 160 0 0 0 0 0), upper := (rows 25 35 28 232 240 224 224 128), lower := (rows 25 35 28 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) }] }

theorem profile30_node5 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,24] 6 224 profile30_node5_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,24] 6 224 profile30_node5_cert).mp (by decide +kernel))

def profile30_node6_cert : Bound 8 := { allowed := (rows 160 144 144 0 0 0 0 0), upper := (rows 25 35 44 216 208 240 208 128), lower := (rows 25 35 44 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) }] }

theorem profile30_node6 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,40] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,40] 6 208 profile30_node6_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,40] 6 208 profile30_node6_cert).mp (by decide +kernel))

def profile30_node8_cert : CutBound 8 := { lost := (rows 0 24 16 0 0 0 0 0), upper := (rows 25 35 76 24 176 160 224 128), lower := (rows 25 35 76 24 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 1 3 13 8 0 255 255 255), good := (rows 239 231 236 236 224 224 224 224) }] }

theorem profile30_node8 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,72,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,72,16] 6 160 profile30_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,72,16] 6 160 profile30_node8_cert).mp (by decide +kernel))

def profile30_node9_cert : CutBound 8 := { lost := (rows 32 8 32 0 0 0 0 0), upper := (rows 25 35 76 40 144 176 208 128), lower := (rows 25 35 76 40 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 5, region := (rows 13 2 13 8 255 0 255 255), good := (rows 221 215 221 221 208 208 208 208) }] }

theorem profile30_node9 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,72,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,72,32] 6 144 profile30_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,72,32] 6 144 profile30_node9_cert).mp (by decide +kernel))

def profile30_node10_cert : CutBound 8 := { lost := (rows 0 8 16 0 0 0 0 0), upper := (rows 25 35 76 136 176 176 240 128), lower := (rows 25 35 76 136 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 1 2 68 255 0 32 64 255), good := (rows 137 171 204 136 136 168 204 136) }] }

theorem profile30_node10 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,72,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,72,128] 6 176 profile30_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,72,128] 6 176 profile30_node10_cert).mp (by decide +kernel))

def profile30_node7_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile30_node7_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node7 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,72] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,72] 6 (by decide) (choices 1) [16,32,128] profile30_node7_route profile30_node7_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node8
  · exact profile30_node9
  · exact profile30_node10

def profile30_node12_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 25 35 100 24 152 168 200 128), lower := (rows 25 35 100 24 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 15 8 0 41 73 255), good := (rows 239 231 228 236 128 160 192 128) }] }

theorem profile30_node12 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96,16] 6 136 profile30_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96,16] 6 136 profile30_node12_cert).mp (by decide +kernel))

def profile30_node14_cert : CutBound 8 := { lost := (rows 0 8 8 0 0 0 0 0), upper := (rows 25 35 100 136 24 176 208 128), lower := (rows 25 35 100 136 24 32 64 128), losses := [{ target := 3, region := (rows 1 3 23 0 16 49 81 255), good := (rows 247 231 228 128 244 160 192 128) }] }

theorem profile30_node14 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96,128,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96,128,8] 6 144 profile30_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96,128,8] 6 144 profile30_node14_cert).mp (by decide +kernel))

def profile30_node15_cert : CutBound 8 := { lost := (rows 32 128 128 0 0 0 0 0), upper := (rows 25 35 100 136 144 56 88 128), lower := (rows 25 35 100 136 144 32 64 128), losses := [{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) },{ target := 7, region := (rows 1 3 7 8 16 33 65 0), good := (rows 127 103 100 8 16 32 64 0) }] }

theorem profile30_node15 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96,128,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96,128,128] 6 24 profile30_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96,128,128] 6 24 profile30_node15_cert).mp (by decide +kernel))

def profile30_node13_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile30_node13_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node13 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96,128] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96,128] 6 (by decide) (choices 1) [8,128] profile30_node13_route profile30_node13_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node14
  · exact profile30_node15

def profile30_node11_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile30_node11_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node11 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,96] 6 (by decide) (choices 1) [16,128] profile30_node11_route profile30_node11_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node12
  · exact profile30_node13

def profile30_node16_cert : Bound 8 := { allowed := (rows 160 144 48 0 0 0 0 0), upper := (rows 25 35 140 248 240 240 240 128), lower := (rows 25 35 140 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) }] }

theorem profile30_node16 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,136] 6 240 profile30_node16_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,136] 6 240 profile30_node16_cert).mp (by decide +kernel))

def profile30_node17_cert : Bound 8 := { allowed := (rows 160 152 16 0 0 0 0 0), upper := (rows 25 35 164 216 216 248 216 128), lower := (rows 25 35 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 38 0 16 32 64 255), good := (rows 145 167 164 128 144 164 192 128) }] }

theorem profile30_node17 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,160] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,160] 6 216 profile30_node17_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,160] 6 216 profile30_node17_cert).mp (by decide +kernel))

def profile30_node18_cert : CutBound 8 := { lost := (rows 0 0 24 0 0 0 0 0), upper := (rows 25 35 196 184 184 184 248 128), lower := (rows 25 35 196 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 68 0 16 32 64 255), good := (rows 145 163 196 128 144 160 196 128) },{ target := 4, region := (rows 1 2 68 8 0 32 64 255), good := (rows 137 163 196 136 128 160 196 128) }] }

theorem profile30_node18 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,192] 6 184 profile30_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33,192] 6 184 profile30_node18_cert).mp (by decide +kernel))

def profile30_node4_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | _ => 0

def profile30_node4_route : Route 8 := (fun mask => match mask with | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile30_node4 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,33] 6 (by decide) (choices 2) [24,40,72,96,136,160,192] profile30_node4_route profile30_node4_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile30_node5
  · exact profile30_node6
  · exact profile30_node7
  · exact profile30_node11
  · exact profile30_node16
  · exact profile30_node17
  · exact profile30_node18

def profile30_node20_cert : Bound 8 := { allowed := (rows 160 144 160 0 0 0 0 0), upper := (rows 25 42 21 232 240 224 224 128), lower := (rows 25 42 21 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) }] }

theorem profile30_node20 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,17] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,17] 6 224 profile30_node20_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,17] 6 224 profile30_node20_cert).mp (by decide +kernel))

def profile30_node21_cert : Bound 8 := { allowed := (rows 160 144 144 0 0 0 0 0), upper := (rows 25 42 37 216 208 240 208 128), lower := (rows 25 42 37 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) }] }

theorem profile30_node21 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,33] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,33] 6 208 profile30_node21_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,33] 6 208 profile30_node21_cert).mp (by decide +kernel))

def profile30_node22_cert : Bound 8 := { allowed := (rows 160 144 136 0 0 0 0 0), upper := (rows 25 42 52 201 209 225 193 128), lower := (rows 25 42 52 8 16 32 64 128), losses := [] }

theorem profile30_node22 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,48] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,48] 6 193 profile30_node22_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,48] 6 193 profile30_node22_cert).mp (by decide +kernel))

def profile30_node24_cert : CutBound 8 := { lost := (rows 0 16 24 0 0 0 0 0), upper := (rows 25 42 69 24 176 160 224 128), lower := (rows 25 42 69 24 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 4, region := (rows 1 11 5 8 0 255 255 255), good := (rows 239 234 231 234 224 224 224 224) }] }

theorem profile30_node24 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,65,16] 6 160 profile30_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,65,16] 6 160 profile30_node24_cert).mp (by decide +kernel))

def profile30_node25_cert : CutBound 8 := { lost := (rows 0 16 8 0 0 0 0 0), upper := (rows 25 42 69 40 144 176 208 128), lower := (rows 25 42 69 40 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 4, region := (rows 1 42 4 42 0 32 64 255), good := (rows 139 170 197 170 128 170 192 128) }] }

theorem profile30_node25 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,65,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,65,32] 6 144 profile30_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,65,32] 6 144 profile30_node25_cert).mp (by decide +kernel))

def profile30_node26_cert : CutBound 8 := { lost := (rows 0 16 8 0 0 0 0 0), upper := (rows 25 42 69 136 176 176 240 128), lower := (rows 25 42 69 136 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 4, region := (rows 1 34 4 255 0 32 64 255), good := (rows 137 170 205 136 136 170 200 136) }] }

theorem profile30_node26 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,65,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,65,128] 6 176 profile30_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,65,128] 6 176 profile30_node26_cert).mp (by decide +kernel))

def profile30_node23_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile30_node23_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node23 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,65] 6 (by decide) (choices 1) [16,32,128] profile30_node23_route profile30_node23_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node24
  · exact profile30_node25
  · exact profile30_node26

def profile30_node27_cert : Bound 8 := { allowed := (rows 160 144 160 0 0 0 0 0), upper := (rows 25 42 84 169 177 161 225 128), lower := (rows 25 42 84 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 255), good := (rows 245 162 212 128 144 160 192 128) }] }

theorem profile30_node27 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,80] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,80] 6 161 profile30_node27_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,80] 6 161 profile30_node27_cert).mp (by decide +kernel))

def profile30_node28_cert : Bound 8 := { allowed := (rows 160 144 144 0 0 0 0 0), upper := (rows 25 42 100 153 145 177 209 128), lower := (rows 25 42 100 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 255), good := (rows 245 162 228 128 144 160 192 128) }] }

theorem profile30_node28 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,96] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,96] 6 145 profile30_node28_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,96] 6 145 profile30_node28_cert).mp (by decide +kernel))

def profile30_node29_cert : Bound 8 := { allowed := (rows 160 144 48 0 0 0 0 0), upper := (rows 25 42 133 248 240 240 240 128), lower := (rows 25 42 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) }] }

theorem profile30_node29 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,129] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,129] 6 240 profile30_node29_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,129] 6 240 profile30_node29_cert).mp (by decide +kernel))

def profile30_node30_cert : Bound 8 := { allowed := (rows 160 144 40 0 0 0 0 0), upper := (rows 25 42 148 233 241 225 225 128), lower := (rows 25 42 148 8 16 32 64 128), losses := [] }

theorem profile30_node30 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,144] 6 225 profile30_node30_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,144] 6 225 profile30_node30_cert).mp (by decide +kernel))

def profile30_node31_cert : Bound 8 := { allowed := (rows 160 144 24 0 0 0 0 0), upper := (rows 25 42 164 217 209 241 209 128), lower := (rows 25 42 164 8 16 32 64 128), losses := [] }

theorem profile30_node31 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,160] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,160] 6 209 profile30_node31_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,160] 6 209 profile30_node31_cert).mp (by decide +kernel))

def profile30_node32_cert : Bound 8 := { allowed := (rows 160 144 48 0 0 0 0 0), upper := (rows 25 42 196 185 177 177 241 128), lower := (rows 25 42 196 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 69 0 17 33 65 255), good := (rows 245 162 196 128 144 160 196 128) }] }

theorem profile30_node32 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,192] 6 177 profile30_node32_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40,192] 6 177 profile30_node32_cert).mp (by decide +kernel))

def profile30_node19_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile30_node19_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node19 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,40] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile30_node19_route profile30_node19_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile30_node20
  · exact profile30_node21
  · exact profile30_node22
  · exact profile30_node23
  · exact profile30_node27
  · exact profile30_node28
  · exact profile30_node29
  · exact profile30_node30
  · exact profile30_node31
  · exact profile30_node32

def profile30_node34_cert : CutBound 8 := { lost := (rows 0 24 0 0 0 0 0 0), upper := (rows 25 67 28 168 176 160 224 128), lower := (rows 25 67 28 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 1 3 4 255 0 255 255 255), good := (rows 235 235 236 232 232 232 232 232) }] }

theorem profile30_node34 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,24] 6 160 profile30_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,24] 6 160 profile30_node34_cert).mp (by decide +kernel))

def profile30_node36_cert : CutBound 8 := { lost := (rows 0 24 16 0 0 0 0 0), upper := (rows 25 67 44 24 176 160 224 128), lower := (rows 25 67 44 24 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 1 3 13 8 0 255 255 255), good := (rows 239 231 236 236 224 224 224 224) }] }

theorem profile30_node36 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,40,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,40,16] 6 160 profile30_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,40,16] 6 160 profile30_node36_cert).mp (by decide +kernel))

def profile30_node37_cert : CutBound 8 := { lost := (rows 0 8 16 0 0 0 0 0), upper := (rows 25 67 44 40 144 176 208 128), lower := (rows 25 67 44 40 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 1 2 44 44 0 32 64 255), good := (rows 141 195 172 172 128 172 192 128) }] }

theorem profile30_node37 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,40,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,40,32] 6 144 profile30_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,40,32] 6 144 profile30_node37_cert).mp (by decide +kernel))

def profile30_node38_cert : CutBound 8 := { lost := (rows 0 8 16 0 0 0 0 0), upper := (rows 25 67 44 136 176 176 240 128), lower := (rows 25 67 44 136 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 1 2 36 255 0 32 64 255), good := (rows 137 203 172 136 136 172 200 136) }] }

theorem profile30_node38 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,40,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,40,128] 6 176 profile30_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,40,128] 6 176 profile30_node38_cert).mp (by decide +kernel))

def profile30_node35_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile30_node35_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node35 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,40] 6 (by decide) (choices 1) [16,32,128] profile30_node35_route profile30_node35_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node36
  · exact profile30_node37
  · exact profile30_node38

def profile30_node39_cert : CutBound 8 := { lost := (rows 0 8 16 0 0 0 0 0), upper := (rows 25 67 140 184 176 176 240 128), lower := (rows 25 67 140 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 1 2 13 8 0 32 64 255), good := (rows 141 199 140 140 128 160 192 128) }] }

theorem profile30_node39 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,136] 6 176 profile30_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,136] 6 176 profile30_node39_cert).mp (by decide +kernel))

def profile30_node40_cert : CutBound 8 := { lost := (rows 0 0 24 0 0 0 0 0), upper := (rows 25 67 164 184 184 184 248 128), lower := (rows 25 67 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 36 0 16 32 64 255), good := (rows 145 195 164 128 144 164 192 128) },{ target := 4, region := (rows 1 2 36 8 0 32 64 255), good := (rows 137 195 164 136 128 164 192 128) }] }

theorem profile30_node40 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,160] 6 184 profile30_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65,160] 6 184 profile30_node40_cert).mp (by decide +kernel))

def profile30_node33_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile30_node33_route : Route 8 := (fun mask => match mask with | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile30_node33 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,65] 6 (by decide) (choices 2) [24,40,136,160] profile30_node33_route profile30_node33_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile30_node34
  · exact profile30_node35
  · exact profile30_node39
  · exact profile30_node40

def profile30_node42_cert : CutBound 8 := { lost := (rows 0 16 8 0 0 0 0 0), upper := (rows 25 74 21 168 176 160 224 128), lower := (rows 25 74 21 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 239 234 234 234 234 234) }] }

theorem profile30_node42 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,17] 6 160 profile30_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,17] 6 160 profile30_node42_cert).mp (by decide +kernel))

def profile30_node44_cert : CutBound 8 := { lost := (rows 0 16 24 0 0 0 0 0), upper := (rows 25 74 37 24 176 160 224 128), lower := (rows 25 74 37 24 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 4, region := (rows 1 11 5 8 0 255 255 255), good := (rows 239 234 231 234 224 224 224 224) }] }

theorem profile30_node44 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,33,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,33,16] 6 160 profile30_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,33,16] 6 160 profile30_node44_cert).mp (by decide +kernel))

def profile30_node45_cert : CutBound 8 := { lost := (rows 32 32 8 0 0 0 0 0), upper := (rows 25 74 37 40 144 176 208 128), lower := (rows 25 74 37 40 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 5, region := (rows 11 11 4 8 255 0 255 255), good := (rows 219 219 215 219 208 208 208 208) }] }

theorem profile30_node45 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,33,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,33,32] 6 144 profile30_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,33,32] 6 144 profile30_node45_cert).mp (by decide +kernel))

def profile30_node46_cert : CutBound 8 := { lost := (rows 0 16 8 0 0 0 0 0), upper := (rows 25 74 37 136 176 176 240 128), lower := (rows 25 74 37 136 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 4, region := (rows 1 66 4 255 0 32 64 255), good := (rows 137 202 173 136 136 168 202 136) }] }

theorem profile30_node46 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,33,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,33,128] 6 176 profile30_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,33,128] 6 176 profile30_node46_cert).mp (by decide +kernel))

def profile30_node43_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile30_node43_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node43 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,33] 6 (by decide) (choices 1) [16,32,128] profile30_node43_route profile30_node43_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node44
  · exact profile30_node45
  · exact profile30_node46

def profile30_node47_cert : Bound 8 := { allowed := (rows 160 176 128 0 0 0 0 0), upper := (rows 25 74 52 169 177 161 225 128), lower := (rows 25 74 52 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 255), good := (rows 245 194 180 128 144 160 192 128) }] }

theorem profile30_node47 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,48] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,48] 6 161 profile30_node47_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,48] 6 161 profile30_node47_cert).mp (by decide +kernel))

def profile30_node48_cert : CutBound 8 := { lost := (rows 0 0 24 0 0 0 0 0), upper := (rows 25 74 133 184 176 176 240 128), lower := (rows 25 74 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 4, region := (rows 1 2 5 8 0 32 64 255), good := (rows 141 202 133 136 128 160 192 128) }] }

theorem profile30_node48 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,129] 6 176 profile30_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,129] 6 176 profile30_node48_cert).mp (by decide +kernel))

def profile30_node49_cert : Bound 8 := { allowed := (rows 160 176 32 0 0 0 0 0), upper := (rows 25 74 148 169 177 161 225 128), lower := (rows 25 74 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 21 0 17 33 65 255), good := (rows 245 194 148 128 148 160 192 128) }] }

theorem profile30_node49 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,144] 6 161 profile30_node49_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,144] 6 161 profile30_node49_cert).mp (by decide +kernel))

def profile30_node50_cert : Bound 8 := { allowed := (rows 160 176 16 0 0 0 0 0), upper := (rows 25 74 164 185 177 177 241 128), lower := (rows 25 74 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 37 0 17 33 65 255), good := (rows 245 194 164 128 144 164 192 128) }] }

theorem profile30_node50 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,160] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,160] 6 177 profile30_node50_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72,160] 6 177 profile30_node50_cert).mp (by decide +kernel))

def profile30_node41_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile30_node41_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node41 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,72] 6 (by decide) (choices 2) [17,33,48,129,144,160] profile30_node41_route profile30_node41_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile30_node42
  · exact profile30_node43
  · exact profile30_node47
  · exact profile30_node48
  · exact profile30_node49
  · exact profile30_node50

def profile30_node52_cert : CutBound 8 := { lost := (rows 0 8 16 0 0 0 0 0), upper := (rows 25 98 13 184 176 176 240 128), lower := (rows 25 98 13 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 255 4 0 255 255 255 255), good := (rows 243 242 247 242 242 242 242 242) },{ target := 4, region := (rows 1 2 5 8 0 32 64 255), good := (rows 141 226 141 136 128 160 192 128) }] }

theorem profile30_node52 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,9] 6 176 profile30_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,9] 6 176 profile30_node52_cert).mp (by decide +kernel))

def profile30_node53_cert : Bound 8 := { allowed := (rows 160 144 160 0 0 0 0 0), upper := (rows 25 98 28 169 177 161 225 128), lower := (rows 25 98 28 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65 255), good := (rows 243 226 148 128 144 160 192 128) }] }

theorem profile30_node53 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,24] 6 161 profile30_node53_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,24] 6 161 profile30_node53_cert).mp (by decide +kernel))

def profile30_node55_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 25 98 37 24 152 168 200 128), lower := (rows 25 98 37 24 16 32 64 128), losses := [{ target := 4, region := (rows 1 15 5 8 0 41 73 255), good := (rows 239 226 231 234 128 160 192 128) }] }

theorem profile30_node55 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33,16] 6 136 profile30_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33,16] 6 136 profile30_node55_cert).mp (by decide +kernel))

def profile30_node57_cert : CutBound 8 := { lost := (rows 0 8 8 0 0 0 0 0), upper := (rows 25 98 37 136 24 176 208 128), lower := (rows 25 98 37 136 24 32 64 128), losses := [{ target := 3, region := (rows 1 23 5 0 16 49 81 255), good := (rows 247 226 231 128 242 160 192 128) }] }

theorem profile30_node57 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33,128,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33,128,8] 6 144 profile30_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33,128,8] 6 144 profile30_node57_cert).mp (by decide +kernel))

def profile30_node58_cert : CutBound 8 := { lost := (rows 32 128 128 0 0 0 0 0), upper := (rows 25 98 37 136 144 56 88 128), lower := (rows 25 98 37 136 144 32 64 128), losses := [{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) },{ target := 7, region := (rows 1 7 5 8 16 33 65 0), good := (rows 127 98 103 8 16 32 64 0) }] }

theorem profile30_node58 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33,128,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33,128,128] 6 24 profile30_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33,128,128] 6 24 profile30_node58_cert).mp (by decide +kernel))

def profile30_node56_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile30_node56_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node56 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33,128] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33,128] 6 (by decide) (choices 1) [8,128] profile30_node56_route profile30_node56_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node57
  · exact profile30_node58

def profile30_node54_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile30_node54_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node54 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,33] 6 (by decide) (choices 1) [16,128] profile30_node54_route profile30_node54_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node55
  · exact profile30_node56

def profile30_node59_cert : Bound 8 := { allowed := (rows 160 144 144 0 0 0 0 0), upper := (rows 25 98 44 153 145 177 209 128), lower := (rows 25 98 44 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65 255), good := (rows 243 226 164 128 144 160 192 128) }] }

theorem profile30_node59 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,40] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,40] 6 145 profile30_node59_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,40] 6 145 profile30_node59_cert).mp (by decide +kernel))

def profile30_node60_cert : CutBound 8 := { lost := (rows 0 0 24 0 0 0 0 0), upper := (rows 25 98 133 184 184 184 248 128), lower := (rows 25 98 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64 255), good := (rows 149 226 133 128 144 160 192 128) },{ target := 4, region := (rows 1 2 5 8 0 32 64 255), good := (rows 141 226 133 136 128 160 192 128) }] }

theorem profile30_node60 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,129] 6 184 profile30_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,129] 6 184 profile30_node60_cert).mp (by decide +kernel))

def profile30_node61_cert : Bound 8 := { allowed := (rows 160 144 48 0 0 0 0 0), upper := (rows 25 98 140 185 177 177 241 128), lower := (rows 25 98 140 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65 255), good := (rows 243 226 132 128 144 160 192 128) }] }

theorem profile30_node61 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,136] 6 177 profile30_node61_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,136] 6 177 profile30_node61_cert).mp (by decide +kernel))

def profile30_node62_cert : Bound 8 := { allowed := (rows 160 152 16 0 0 0 0 0), upper := (rows 25 98 164 153 153 185 217 128), lower := (rows 25 98 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 38 0 16 32 64 255), good := (rows 145 230 164 128 144 164 192 128) }] }

theorem profile30_node62 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,160] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,160] 6 153 profile30_node62_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96,160] 6 153 profile30_node62_cert).mp (by decide +kernel))

def profile30_node51_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile30_node51_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile30_node51 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,96] 6 (by decide) (choices 2) [9,24,33,40,129,136,160] profile30_node51_route profile30_node51_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile30_node52
  · exact profile30_node53
  · exact profile30_node54
  · exact profile30_node59
  · exact profile30_node60
  · exact profile30_node61
  · exact profile30_node62

def profile30_node63_cert : CutBound 8 := { lost := (rows 0 24 0 0 0 0 0 0), upper := (rows 25 131 252 248 248 248 248 128), lower := (rows 25 131 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64 255), good := (rows 147 131 132 128 144 160 192 128) },{ target := 4, region := (rows 1 3 4 8 0 32 64 255), good := (rows 139 131 132 136 128 160 192 128) }] }

theorem profile30_node63 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,129] 6 248 profile30_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,129] 6 248 profile30_node63_cert).mp (by decide +kernel))

def profile30_node64_cert : CutBound 8 := { lost := (rows 0 16 8 0 0 0 0 0), upper := (rows 25 138 245 249 241 241 241 128), lower := (rows 25 138 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 255), good := (rows 245 130 132 128 144 160 192 128) },{ target := 4, region := (rows 1 11 4 8 0 32 64 255), good := (rows 139 138 132 138 128 160 192 128) }] }

theorem profile30_node64 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,136] 6 241 profile30_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,136] 6 241 profile30_node64_cert).mp (by decide +kernel))

def profile30_node65_cert : CutBound 8 := { lost := (rows 0 24 0 0 0 0 0 0), upper := (rows 25 162 253 249 249 249 249 128), lower := (rows 25 162 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 64 255), good := (rows 145 162 132 128 144 162 192 128) },{ target := 4, region := (rows 1 34 4 8 0 32 64 255), good := (rows 137 162 132 136 128 162 192 128) }] }

theorem profile30_node65 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,160] 6 249 profile30_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,160] 6 249 profile30_node65_cert).mp (by decide +kernel))

def profile30_node66_cert : CutBound 8 := { lost := (rows 0 24 0 0 0 0 0 0), upper := (rows 25 194 189 185 185 185 249 128), lower := (rows 25 194 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 66 4 0 16 32 64 255), good := (rows 145 194 132 128 144 160 194 128) },{ target := 4, region := (rows 1 66 4 8 0 32 64 255), good := (rows 137 194 132 136 128 160 194 128) }] }

theorem profile30_node66 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,192] 6 185 profile30_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24,192] 6 185 profile30_node66_cert).mp (by decide +kernel))

def profile30_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile30_node1_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile30_node1 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [24] 6 (by decide) (choices 2) [9,24,33,40,65,72,96,129,136,160,192] profile30_node1_route profile30_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile30_node2
  · exact profile30_node3
  · exact profile30_node4
  · exact profile30_node19
  · exact profile30_node33
  · exact profile30_node41
  · exact profile30_node51
  · exact profile30_node63
  · exact profile30_node64
  · exact profile30_node65
  · exact profile30_node66

def profile30_node68_cert : CutBound 8 := { lost := (rows 0 16 8 0 0 0 0 0), upper := (rows 73 11 180 184 176 176 240 128), lower := (rows 73 11 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 247 244 244 244 244 244 244) },{ target := 4, region := (rows 1 3 4 8 0 32 64 255), good := (rows 203 139 132 136 128 160 192 128) }] }

theorem profile30_node68 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,9] 6 176 profile30_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,9] 6 176 profile30_node68_cert).mp (by decide +kernel))

def profile30_node70_cert : CutBound 8 := { lost := (rows 16 8 0 0 0 0 0 0), upper := (rows 73 19 28 168 176 160 224 128), lower := (rows 73 19 28 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile30_node70 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,24] 6 160 profile30_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,24] 6 160 profile30_node70_cert).mp (by decide +kernel))

def profile30_node72_cert : CutBound 8 := { lost := (rows 16 8 16 0 0 0 0 0), upper := (rows 73 19 44 24 176 160 224 128), lower := (rows 73 19 44 24 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 13 2 13 8 0 255 255 255), good := (rows 237 231 237 237 224 224 224 224) }] }

theorem profile30_node72 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,40,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,40,16] 6 160 profile30_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,40,16] 6 160 profile30_node72_cert).mp (by decide +kernel))

def profile30_node73_cert : CutBound 8 := { lost := (rows 0 8 16 0 0 0 0 0), upper := (rows 73 19 44 40 144 176 208 128), lower := (rows 73 19 44 40 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 1 2 44 44 0 32 64 255), good := (rows 205 131 172 172 128 172 192 128) }] }

theorem profile30_node73 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,40,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,40,32] 6 144 profile30_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,40,32] 6 144 profile30_node73_cert).mp (by decide +kernel))

def profile30_node74_cert : CutBound 8 := { lost := (rows 16 8 16 0 0 0 0 0), upper := (rows 73 19 44 136 176 176 240 128), lower := (rows 73 19 44 136 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 65 2 36 255 0 32 64 255), good := (rows 201 139 172 136 136 172 201 136) }] }

theorem profile30_node74 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,40,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,40,128] 6 176 profile30_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,40,128] 6 176 profile30_node74_cert).mp (by decide +kernel))

def profile30_node71_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile30_node71_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node71 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,40] 6 (by decide) (choices 1) [16,32,128] profile30_node71_route profile30_node71_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node72
  · exact profile30_node73
  · exact profile30_node74

def profile30_node76_cert : CutBound 8 := { lost := (rows 48 32 0 0 0 0 0 0), upper := (rows 73 19 52 40 152 168 200 128), lower := (rows 73 19 52 40 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 9 11 4 8 25 0 73 255), good := (rows 219 211 148 219 144 128 192 128) }] }

theorem profile30_node76 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,48,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,48,32] 6 136 profile30_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,48,32] 6 136 profile30_node76_cert).mp (by decide +kernel))

def profile30_node77_cert : CutBound 8 := { lost := (rows 48 0 0 0 0 0 0 0), upper := (rows 73 19 52 136 184 168 232 128), lower := (rows 73 19 52 136 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 65 2 4 255 16 0 64 255), good := (rows 201 155 156 136 152 136 201 136) }] }

theorem profile30_node77 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,48,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,48,128] 6 168 profile30_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,48,128] 6 168 profile30_node77_cert).mp (by decide +kernel))

def profile30_node75_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0

def profile30_node75_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node75 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,48] 6 (by decide) (choices 1) [32,128] profile30_node75_route profile30_node75_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node76
  · exact profile30_node77

def profile30_node78_cert : CutBound 8 := { lost := (rows 0 8 16 0 0 0 0 0), upper := (rows 73 19 140 184 176 176 240 128), lower := (rows 73 19 140 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) },{ target := 4, region := (rows 1 2 13 8 0 32 64 255), good := (rows 205 135 140 140 128 160 192 128) }] }

theorem profile30_node78 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,136] 6 176 profile30_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,136] 6 176 profile30_node78_cert).mp (by decide +kernel))

def profile30_node79_cert : CutBound 8 := { lost := (rows 16 0 8 0 0 0 0 0), upper := (rows 73 19 148 168 184 168 232 128), lower := (rows 73 19 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 22 0 16 32 64 255), good := (rows 193 151 148 128 148 160 192 128) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile30_node79 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,144] 6 168 profile30_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,144] 6 168 profile30_node79_cert).mp (by decide +kernel))

def profile30_node80_cert : CutBound 8 := { lost := (rows 0 0 24 0 0 0 0 0), upper := (rows 73 19 164 184 184 184 248 128), lower := (rows 73 19 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 36 0 16 32 64 255), good := (rows 193 147 164 128 144 164 192 128) },{ target := 4, region := (rows 1 2 36 8 0 32 64 255), good := (rows 201 131 164 136 128 164 192 128) }] }

theorem profile30_node80 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,160] 6 184 profile30_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17,160] 6 184 profile30_node80_cert).mp (by decide +kernel))

def profile30_node69_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile30_node69_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node69 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,17] 6 (by decide) (choices 2) [24,40,48,136,144,160] profile30_node69_route profile30_node69_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile30_node70
  · exact profile30_node71
  · exact profile30_node75
  · exact profile30_node78
  · exact profile30_node79
  · exact profile30_node80

def profile30_node82_cert : CutBound 8 := { lost := (rows 16 0 8 0 0 0 0 0), upper := (rows 73 26 21 168 176 160 224 128), lower := (rows 73 26 21 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile30_node82 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,17] 6 160 profile30_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,17] 6 160 profile30_node82_cert).mp (by decide +kernel))

def profile30_node84_cert : CutBound 8 := { lost := (rows 16 0 24 0 0 0 0 0), upper := (rows 73 26 37 24 176 160 224 128), lower := (rows 73 26 37 24 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 4, region := (rows 11 2 15 8 0 255 255 255), good := (rows 237 239 229 237 224 224 224 224) }] }

theorem profile30_node84 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,33,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,33,16] 6 160 profile30_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,33,16] 6 160 profile30_node84_cert).mp (by decide +kernel))

def profile30_node85_cert : CutBound 8 := { lost := (rows 32 32 8 0 0 0 0 0), upper := (rows 73 26 37 40 144 176 208 128), lower := (rows 73 26 37 40 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 5, region := (rows 11 11 4 8 255 0 255 255), good := (rows 219 219 215 219 208 208 208 208) }] }

theorem profile30_node85 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,33,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,33,32] 6 144 profile30_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,33,32] 6 144 profile30_node85_cert).mp (by decide +kernel))

def profile30_node86_cert : CutBound 8 := { lost := (rows 16 0 8 0 0 0 0 0), upper := (rows 73 26 37 136 176 176 240 128), lower := (rows 73 26 37 136 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 4, region := (rows 65 2 4 255 0 32 64 255), good := (rows 201 138 173 136 136 168 201 136) }] }

theorem profile30_node86 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,33,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,33,128] 6 176 profile30_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,33,128] 6 176 profile30_node86_cert).mp (by decide +kernel))

def profile30_node83_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile30_node83_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node83 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,33] 6 (by decide) (choices 1) [16,32,128] profile30_node83_route profile30_node83_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node84
  · exact profile30_node85
  · exact profile30_node86

def profile30_node87_cert : Bound 8 := { allowed := (rows 176 160 128 0 0 0 0 0), upper := (rows 73 26 52 169 177 161 225 128), lower := (rows 73 26 52 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 255), good := (rows 245 146 180 128 144 160 192 128) }] }

theorem profile30_node87 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,48] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,48] 6 161 profile30_node87_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,48] 6 161 profile30_node87_cert).mp (by decide +kernel))

def profile30_node88_cert : CutBound 8 := { lost := (rows 0 0 24 0 0 0 0 0), upper := (rows 73 26 133 184 176 176 240 128), lower := (rows 73 26 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 255 255 255 255), good := (rows 245 242 245 240 240 240 240 240) },{ target := 4, region := (rows 1 2 5 8 0 32 64 255), good := (rows 205 138 133 136 128 160 192 128) }] }

theorem profile30_node88 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,129] 6 176 profile30_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,129] 6 176 profile30_node88_cert).mp (by decide +kernel))

def profile30_node89_cert : Bound 8 := { allowed := (rows 176 160 32 0 0 0 0 0), upper := (rows 73 26 148 169 177 161 225 128), lower := (rows 73 26 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 23 0 17 33 65 255), good := (rows 245 150 148 128 148 160 192 128) }] }

theorem profile30_node89 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,144] 6 161 profile30_node89_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,144] 6 161 profile30_node89_cert).mp (by decide +kernel))

def profile30_node90_cert : Bound 8 := { allowed := (rows 176 160 16 0 0 0 0 0), upper := (rows 73 26 164 185 177 177 241 128), lower := (rows 73 26 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 37 0 17 33 65 255), good := (rows 245 146 164 128 144 164 192 128) }] }

theorem profile30_node90 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,160] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,160] 6 177 profile30_node90_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24,160] 6 177 profile30_node90_cert).mp (by decide +kernel))

def profile30_node81_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile30_node81_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node81 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,24] 6 (by decide) (choices 2) [17,33,48,129,144,160] profile30_node81_route profile30_node81_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile30_node82
  · exact profile30_node83
  · exact profile30_node87
  · exact profile30_node88
  · exact profile30_node89
  · exact profile30_node90

def profile30_node92_cert : CutBound 8 := { lost := (rows 0 8 16 0 0 0 0 0), upper := (rows 73 50 13 184 176 176 240 128), lower := (rows 73 50 13 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 255 4 0 255 255 255 255), good := (rows 243 242 247 242 242 242 242 242) },{ target := 4, region := (rows 1 2 5 8 0 32 64 255), good := (rows 205 162 141 136 128 160 192 128) }] }

theorem profile30_node92 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,9] 6 176 profile30_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,9] 6 176 profile30_node92_cert).mp (by decide +kernel))

def profile30_node94_cert : CutBound 8 := { lost := (rows 48 0 32 0 0 0 0 0), upper := (rows 73 50 21 40 152 168 200 128), lower := (rows 73 50 21 40 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 9 2 13 8 25 0 73 255), good := (rows 221 146 213 221 144 128 192 128) }] }

theorem profile30_node94 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,17,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,17,32] 6 136 profile30_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,17,32] 6 136 profile30_node94_cert).mp (by decide +kernel))

def profile30_node95_cert : CutBound 8 := { lost := (rows 48 0 0 0 0 0 0 0), upper := (rows 73 50 21 136 184 168 232 128), lower := (rows 73 50 21 136 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) },{ target := 5, region := (rows 65 2 4 255 16 0 64 255), good := (rows 201 154 157 136 152 136 201 136) }] }

theorem profile30_node95 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,17,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,17,128] 6 168 profile30_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,17,128] 6 168 profile30_node95_cert).mp (by decide +kernel))

def profile30_node93_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0

def profile30_node93_route : Route 8 := (fun mask => (mask,id))

theorem profile30_node93 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,17] 6 (by decide) (choices 1) [32,128] profile30_node93_route profile30_node93_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node94
  · exact profile30_node95

def profile30_node96_cert : Bound 8 := { allowed := (rows 176 128 160 0 0 0 0 0), upper := (rows 73 50 28 169 177 161 225 128), lower := (rows 73 50 28 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65 255), good := (rows 243 178 148 128 144 160 192 128) }] }

theorem profile30_node96 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,24] 6 161 profile30_node96_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,24] 6 161 profile30_node96_cert).mp (by decide +kernel))

def profile30_node97_cert : CutBound 8 := { lost := (rows 0 8 8 0 0 0 0 0), upper := (rows 73 50 52 137 153 169 201 128), lower := (rows 73 50 52 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 6 6 0 16 32 64 255), good := (rows 193 182 182 128 144 160 192 128) }] }

theorem profile30_node97 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,48] 6 137 profile30_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,48] 6 137 profile30_node97_cert).mp (by decide +kernel))

def profile30_node98_cert : CutBound 8 := { lost := (rows 0 0 24 0 0 0 0 0), upper := (rows 73 50 133 184 184 184 248 128), lower := (rows 73 50 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64 255), good := (rows 197 178 133 128 144 160 192 128) },{ target := 4, region := (rows 1 2 5 8 0 32 64 255), good := (rows 205 162 133 136 128 160 192 128) }] }

theorem profile30_node98 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,129] 6 184 profile30_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,129] 6 184 profile30_node98_cert).mp (by decide +kernel))

def profile30_node99_cert : Bound 8 := { allowed := (rows 176 128 48 0 0 0 0 0), upper := (rows 73 50 140 185 177 177 241 128), lower := (rows 73 50 140 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65 255), good := (rows 243 178 132 128 144 160 192 128) }] }

theorem profile30_node99 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,136] 6 177 profile30_node99_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,136] 6 177 profile30_node99_cert).mp (by decide +kernel))

def profile30_node100_cert : Bound 8 := { allowed := (rows 176 136 32 0 0 0 0 0), upper := (rows 73 50 148 169 185 169 233 128), lower := (rows 73 50 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 22 0 16 32 64 255), good := (rows 193 182 148 128 148 160 192 128) }] }

theorem profile30_node100 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,144] 6 169 profile30_node100_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48,144] 6 169 profile30_node100_cert).mp (by decide +kernel))

def profile30_node91_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile30_node91_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile30_node91 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,48] 6 (by decide) (choices 2) [9,17,24,48,129,136,144] profile30_node91_route profile30_node91_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile30_node92
  · exact profile30_node93
  · exact profile30_node96
  · exact profile30_node97
  · exact profile30_node98
  · exact profile30_node99
  · exact profile30_node100

def profile30_node101_cert : CutBound 8 := { lost := (rows 0 24 0 0 0 0 0 0), upper := (rows 73 131 188 184 184 184 248 128), lower := (rows 73 131 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64 255), good := (rows 195 131 132 128 144 160 192 128) },{ target := 4, region := (rows 1 3 4 8 0 32 64 255), good := (rows 203 131 132 136 128 160 192 128) }] }

theorem profile30_node101 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,129] 6 184 profile30_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,129] 6 184 profile30_node101_cert).mp (by decide +kernel))

def profile30_node102_cert : CutBound 8 := { lost := (rows 0 16 8 0 0 0 0 0), upper := (rows 73 138 181 185 177 177 241 128), lower := (rows 73 138 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 255), good := (rows 245 130 132 128 144 160 192 128) },{ target := 4, region := (rows 1 11 4 8 0 32 64 255), good := (rows 203 138 132 138 128 160 192 128) }] }

theorem profile30_node102 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,136] 6 177 profile30_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,136] 6 177 profile30_node102_cert).mp (by decide +kernel))

def profile30_node103_cert : CutBound 8 := { lost := (rows 0 40 0 0 0 0 0 0), upper := (rows 73 146 189 185 185 185 249 128), lower := (rows 73 146 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 18 4 0 16 32 64 255), good := (rows 193 146 132 128 146 160 192 128) },{ target := 5, region := (rows 1 18 4 8 16 0 64 255), good := (rows 201 146 132 136 146 128 192 128) }] }

theorem profile30_node103 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,144] 6 185 profile30_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72,144] 6 185 profile30_node103_cert).mp (by decide +kernel))

def profile30_node67_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 65 => 6 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile30_node67_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile30_node67 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [72] 6 (by decide) (choices 2) [9,17,24,48,129,136,144] profile30_node67_route profile30_node67_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile30_node68
  · exact profile30_node69
  · exact profile30_node81
  · exact profile30_node91
  · exact profile30_node101
  · exact profile30_node102
  · exact profile30_node103

def profile30_node104_cert : CutBound 8 := { lost := (rows 48 0 0 0 0 0 0 0), upper := (rows 137 251 253 249 249 249 249 128), lower := (rows 137 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 9 2 4 8 0 32 64 255), good := (rows 137 130 132 137 128 160 192 128) },{ target := 5, region := (rows 9 2 4 8 16 0 64 255), good := (rows 137 130 132 137 144 128 192 128) }] }

theorem profile30_node104 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [136] 6 249 profile30_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [136] 6 249 profile30_node104_cert).mp (by decide +kernel))

def profile30_node105_cert : CutBound 8 := { lost := (rows 24 0 0 0 0 0 0 0), upper := (rows 193 187 189 185 185 185 249 128), lower := (rows 193 2 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 65 2 4 0 16 32 64 255), good := (rows 193 130 132 128 144 160 193 128) },{ target := 4, region := (rows 65 2 4 8 0 32 64 255), good := (rows 193 130 132 136 128 160 193 128) }] }

theorem profile30_node105 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [192] 6 185 profile30_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [192] 6 185 profile30_node105_cert).mp (by decide +kernel))

def profile30_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile30_node0_route : Route 8 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 96 => (72,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 160 => (136,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile30_node0 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [] 6 (by decide) (choices 2) [24,72,136,192] profile30_node0_route profile30_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile30_node1
  · exact profile30_node67
  · exact profile30_node104
  · exact profile30_node105

theorem profile30 : Upper (D (n:=8) [33,32,32,18,18,18,17,2]) (R (n:=8) [33,32,32,18,18,18,17,2]) [] 6 := profile30_node0


#print axioms profile30
end Delivery.SmallBudgetTenFinite8
