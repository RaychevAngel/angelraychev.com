import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile31_node2_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 25 26 236 232 248 232 232 128), lower := (rows 25 26 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) }] }

theorem profile31_node2 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,24] 6 232 profile31_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,24] 6 232 profile31_node2_cert).mp (by decide +kernel))

def profile31_node4_cert : Bound 8 := { allowed := (rows 160 144 160 0 0 0 0 0), upper := (rows 25 42 28 232 240 224 224 128), lower := (rows 25 42 28 8 16 32 64 128), losses := [] }

theorem profile31_node4 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,24] 6 224 profile31_node4_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,24] 6 224 profile31_node4_cert).mp (by decide +kernel))

def profile31_node5_cert : Bound 8 := { allowed := (rows 160 144 144 0 0 0 0 0), upper := (rows 25 42 44 216 208 240 208 128), lower := (rows 25 42 44 8 16 32 64 128), losses := [] }

theorem profile31_node5 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,40] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,40] 6 208 profile31_node5_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,40] 6 208 profile31_node5_cert).mp (by decide +kernel))

def profile31_node6_cert : Bound 8 := { allowed := (rows 160 144 136 0 0 0 0 0), upper := (rows 25 42 52 200 216 232 200 128), lower := (rows 25 42 52 8 16 32 64 128), losses := [] }

theorem profile31_node6 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,48] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,48] 6 200 profile31_node6_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,48] 6 200 profile31_node6_cert).mp (by decide +kernel))

def profile31_node8_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 25 42 76 24 176 160 224 128), lower := (rows 25 42 76 24 16 32 64 128), losses := [{ target := 4, region := (rows 1 15 15 8 0 255 255 255), good := (rows 239 238 238 238 224 224 224 224) }] }

theorem profile31_node8 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,72,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,72,16] 6 160 profile31_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,72,16] 6 160 profile31_node8_cert).mp (by decide +kernel))

def profile31_node9_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 25 42 76 40 144 176 208 128), lower := (rows 25 42 76 40 16 32 64 128), losses := [{ target := 4, region := (rows 1 42 4 42 0 32 64 255), good := (rows 139 170 206 170 128 170 192 128) }] }

theorem profile31_node9 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,72,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,72,32] 6 144 profile31_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,72,32] 6 144 profile31_node9_cert).mp (by decide +kernel))

def profile31_node10_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 25 42 76 136 176 176 240 128), lower := (rows 25 42 76 136 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 68 255 0 32 64 255), good := (rows 137 170 204 136 136 170 204 136) }] }

theorem profile31_node10 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,72,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,72,128] 6 176 profile31_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,72,128] 6 176 profile31_node10_cert).mp (by decide +kernel))

def profile31_node7_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile31_node7_route : Route 8 := (fun mask => (mask,id))

theorem profile31_node7 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,72] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,72] 6 (by decide) (choices 1) [16,32,128] profile31_node7_route profile31_node7_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node8
  · exact profile31_node9
  · exact profile31_node10

def profile31_node11_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 25 42 84 168 184 168 232 128), lower := (rows 25 42 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) }] }

theorem profile31_node11 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,80] 6 168 profile31_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,80] 6 168 profile31_node11_cert).mp (by decide +kernel))

def profile31_node12_cert : CutBound 8 := { lost := (rows 32 0 0 0 0 0 0 0), upper := (rows 25 42 100 152 152 184 216 128), lower := (rows 25 42 100 8 16 32 64 128), losses := [{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile31_node12 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,96] 6 152 profile31_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,96] 6 152 profile31_node12_cert).mp (by decide +kernel))

def profile31_node13_cert : Bound 8 := { allowed := (rows 160 144 48 0 0 0 0 0), upper := (rows 25 42 140 248 240 240 240 128), lower := (rows 25 42 140 8 16 32 64 128), losses := [] }

theorem profile31_node13 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,136] 6 240 profile31_node13_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,136] 6 240 profile31_node13_cert).mp (by decide +kernel))

def profile31_node14_cert : Bound 8 := { allowed := (rows 160 144 40 0 0 0 0 0), upper := (rows 25 42 148 232 248 232 232 128), lower := (rows 25 42 148 8 16 32 64 128), losses := [] }

theorem profile31_node14 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,144] 6 232 profile31_node14_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,144] 6 232 profile31_node14_cert).mp (by decide +kernel))

def profile31_node15_cert : Bound 8 := { allowed := (rows 160 144 24 0 0 0 0 0), upper := (rows 25 42 164 216 216 248 216 128), lower := (rows 25 42 164 8 16 32 64 128), losses := [] }

theorem profile31_node15 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,160] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,160] 6 216 profile31_node15_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,160] 6 216 profile31_node15_cert).mp (by decide +kernel))

def profile31_node16_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 25 42 196 184 184 184 248 128), lower := (rows 25 42 196 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 68 0 16 32 64 255), good := (rows 145 162 196 128 144 160 196 128) }] }

theorem profile31_node16 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,192] 6 184 profile31_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40,192] 6 184 profile31_node16_cert).mp (by decide +kernel))

def profile31_node3_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | _ => 0

def profile31_node3_route : Route 8 := (fun mask => (mask,id))

theorem profile31_node3 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,40] 6 (by decide) (choices 2) [24,40,48,72,80,96,136,144,160,192] profile31_node3_route profile31_node3_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node4
  · exact profile31_node5
  · exact profile31_node6
  · exact profile31_node7
  · exact profile31_node11
  · exact profile31_node12
  · exact profile31_node13
  · exact profile31_node14
  · exact profile31_node15
  · exact profile31_node16

def profile31_node17_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 25 50 236 232 248 232 232 128), lower := (rows 25 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) }] }

theorem profile31_node17 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,48] 6 232 profile31_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,48] 6 232 profile31_node17_cert).mp (by decide +kernel))

def profile31_node19_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 25 74 28 168 176 160 224 128), lower := (rows 25 74 28 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) }] }

theorem profile31_node19 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,24] 6 160 profile31_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,24] 6 160 profile31_node19_cert).mp (by decide +kernel))

def profile31_node21_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 25 74 44 24 176 160 224 128), lower := (rows 25 74 44 24 16 32 64 128), losses := [{ target := 4, region := (rows 1 15 15 8 0 255 255 255), good := (rows 239 238 238 238 224 224 224 224) }] }

theorem profile31_node21 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,40,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,40,16] 6 160 profile31_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,40,16] 6 160 profile31_node21_cert).mp (by decide +kernel))

def profile31_node22_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 25 74 44 40 144 176 208 128), lower := (rows 25 74 44 40 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 44 44 0 32 64 255), good := (rows 141 206 172 172 128 172 192 128) }] }

theorem profile31_node22 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,40,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,40,32] 6 144 profile31_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,40,32] 6 144 profile31_node22_cert).mp (by decide +kernel))

def profile31_node23_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 25 74 44 136 176 176 240 128), lower := (rows 25 74 44 136 16 32 64 128), losses := [{ target := 4, region := (rows 1 66 36 255 0 32 64 255), good := (rows 137 202 172 136 136 172 202 136) }] }

theorem profile31_node23 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,40,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,40,128] 6 176 profile31_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,40,128] 6 176 profile31_node23_cert).mp (by decide +kernel))

def profile31_node20_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile31_node20_route : Route 8 := (fun mask => (mask,id))

theorem profile31_node20 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,40] 6 (by decide) (choices 1) [16,32,128] profile31_node20_route profile31_node20_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node21
  · exact profile31_node22
  · exact profile31_node23

def profile31_node24_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 25 74 52 168 184 168 232 128), lower := (rows 25 74 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) }] }

theorem profile31_node24 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,48] 6 168 profile31_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,48] 6 168 profile31_node24_cert).mp (by decide +kernel))

def profile31_node25_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 25 74 140 184 176 176 240 128), lower := (rows 25 74 140 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 15 8 0 32 64 255), good := (rows 141 206 140 140 128 160 192 128) }] }

theorem profile31_node25 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,136] 6 176 profile31_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,136] 6 176 profile31_node25_cert).mp (by decide +kernel))

def profile31_node26_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 25 74 148 168 184 168 232 128), lower := (rows 25 74 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 21 0 16 32 64 255), good := (rows 149 194 148 128 148 160 192 128) }] }

theorem profile31_node26 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,144] 6 168 profile31_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,144] 6 168 profile31_node26_cert).mp (by decide +kernel))

def profile31_node27_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 25 74 164 184 184 184 248 128), lower := (rows 25 74 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 36 0 16 32 64 255), good := (rows 145 194 164 128 144 164 192 128) }] }

theorem profile31_node27 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,160] 6 184 profile31_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72,160] 6 184 profile31_node27_cert).mp (by decide +kernel))

def profile31_node18_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile31_node18_route : Route 8 := (fun mask => (mask,id))

theorem profile31_node18 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,72] 6 (by decide) (choices 2) [24,40,48,136,144,160] profile31_node18_route profile31_node18_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node19
  · exact profile31_node20
  · exact profile31_node24
  · exact profile31_node25
  · exact profile31_node26
  · exact profile31_node27

def profile31_node28_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 25 82 172 168 184 168 232 128), lower := (rows 25 82 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) }] }

theorem profile31_node28 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,80] 6 168 profile31_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,80] 6 168 profile31_node28_cert).mp (by decide +kernel))

def profile31_node30_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 25 98 28 168 184 168 232 128), lower := (rows 25 98 28 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) }] }

theorem profile31_node30 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,24] 6 168 profile31_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,24] 6 168 profile31_node30_cert).mp (by decide +kernel))

def profile31_node31_cert : CutBound 8 := { lost := (rows 32 0 0 0 0 0 0 0), upper := (rows 25 98 44 152 152 184 216 128), lower := (rows 25 98 44 8 16 32 64 128), losses := [{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile31_node31 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,40] 6 152 profile31_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,40] 6 152 profile31_node31_cert).mp (by decide +kernel))

def profile31_node32_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 25 98 52 136 152 168 200 128), lower := (rows 25 98 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) }] }

theorem profile31_node32 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,48] 6 136 profile31_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,48] 6 136 profile31_node32_cert).mp (by decide +kernel))

def profile31_node33_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 25 98 140 184 184 184 248 128), lower := (rows 25 98 140 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 13 8 0 32 64 255), good := (rows 141 226 140 140 128 160 192 128) }] }

theorem profile31_node33 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,136] 6 184 profile31_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,136] 6 184 profile31_node33_cert).mp (by decide +kernel))

def profile31_node34_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 25 98 148 168 184 168 232 128), lower := (rows 25 98 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 21 0 16 32 64 255), good := (rows 149 226 148 128 148 160 192 128) }] }

theorem profile31_node34 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,144] 6 168 profile31_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,144] 6 168 profile31_node34_cert).mp (by decide +kernel))

def profile31_node35_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 25 98 164 152 152 184 216 128), lower := (rows 25 98 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 38 0 16 32 64 255), good := (rows 145 230 164 128 144 164 192 128) }] }

theorem profile31_node35 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,160] 6 152 profile31_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96,160] 6 152 profile31_node35_cert).mp (by decide +kernel))

def profile31_node29_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile31_node29_route : Route 8 := (fun mask => (mask,id))

theorem profile31_node29 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,96] 6 (by decide) (choices 2) [24,40,48,136,144,160] profile31_node29_route profile31_node29_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node30
  · exact profile31_node31
  · exact profile31_node32
  · exact profile31_node33
  · exact profile31_node34
  · exact profile31_node35

def profile31_node36_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 25 138 252 248 248 248 248 128), lower := (rows 25 138 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 11 4 8 0 32 64 255), good := (rows 139 138 132 138 128 160 192 128) }] }

theorem profile31_node36 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,136] 6 248 profile31_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,136] 6 248 profile31_node36_cert).mp (by decide +kernel))

def profile31_node37_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 25 146 236 232 248 232 232 128), lower := (rows 25 146 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 19 4 0 16 32 64 255), good := (rows 147 146 132 128 146 160 192 128) }] }

theorem profile31_node37 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,144] 6 232 profile31_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,144] 6 232 profile31_node37_cert).mp (by decide +kernel))

def profile31_node38_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 25 162 252 248 248 248 248 128), lower := (rows 25 162 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 64 255), good := (rows 145 162 132 128 144 162 192 128) }] }

theorem profile31_node38 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,160] 6 248 profile31_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,160] 6 248 profile31_node38_cert).mp (by decide +kernel))

def profile31_node39_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 25 194 188 184 184 184 248 128), lower := (rows 25 194 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 66 4 0 16 32 64 255), good := (rows 145 194 132 128 144 160 194 128) }] }

theorem profile31_node39 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,192] 6 184 profile31_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24,192] 6 184 profile31_node39_cert).mp (by decide +kernel))

def profile31_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile31_node1_route : Route 8 := (fun mask => (mask,id))

theorem profile31_node1 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [24] 6 (by decide) (choices 2) [24,40,48,72,80,96,136,144,160,192] profile31_node1_route profile31_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node2
  · exact profile31_node3
  · exact profile31_node17
  · exact profile31_node18
  · exact profile31_node28
  · exact profile31_node29
  · exact profile31_node36
  · exact profile31_node37
  · exact profile31_node38
  · exact profile31_node39

def profile31_node41_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 49 26 236 232 248 232 232 128), lower := (rows 49 26 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) }] }

theorem profile31_node41 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,24] 6 232 profile31_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,24] 6 232 profile31_node41_cert).mp (by decide +kernel))

def profile31_node42_cert : CutBound 8 := { lost := (rows 8 8 0 0 0 0 0 0), upper := (rows 49 50 204 200 216 232 200 128), lower := (rows 49 50 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 3 3 4 0 16 32 64 255), good := (rows 179 179 132 128 144 160 192 128) }] }

theorem profile31_node42 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,48] 6 200 profile31_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,48] 6 200 profile31_node42_cert).mp (by decide +kernel))

def profile31_node44_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 49 74 28 168 184 168 232 128), lower := (rows 49 74 28 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) }] }

theorem profile31_node44 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,24] 6 168 profile31_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,24] 6 168 profile31_node44_cert).mp (by decide +kernel))

def profile31_node45_cert : CutBound 8 := { lost := (rows 8 0 8 0 0 0 0 0), upper := (rows 49 74 52 136 152 168 200 128), lower := (rows 49 74 52 8 16 32 64 128), losses := [{ target := 3, region := (rows 5 2 5 0 16 32 64 255), good := (rows 181 194 181 128 144 160 192 128) }] }

theorem profile31_node45 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,48] 6 136 profile31_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,48] 6 136 profile31_node45_cert).mp (by decide +kernel))

def profile31_node46_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 49 74 140 184 184 184 248 128), lower := (rows 49 74 140 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 14 8 0 32 64 255), good := (rows 161 206 140 140 128 160 192 128) }] }

theorem profile31_node46 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,136] 6 184 profile31_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,136] 6 184 profile31_node46_cert).mp (by decide +kernel))

def profile31_node47_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 49 74 148 168 184 168 232 128), lower := (rows 49 74 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 21 0 16 32 64 255), good := (rows 181 194 148 128 148 160 192 128) }] }

theorem profile31_node47 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,144] 6 168 profile31_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72,144] 6 168 profile31_node47_cert).mp (by decide +kernel))

def profile31_node43_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile31_node43_route : Route 8 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile31_node43 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,72] 6 (by decide) (choices 2) [24,48,136,144] profile31_node43_route profile31_node43_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile31_node44
  · exact profile31_node45
  · exact profile31_node46
  · exact profile31_node47

def profile31_node48_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 49 82 172 168 184 168 232 128), lower := (rows 49 82 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) }] }

theorem profile31_node48 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,80] 6 168 profile31_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,80] 6 168 profile31_node48_cert).mp (by decide +kernel))

def profile31_node49_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 49 138 252 248 248 248 248 128), lower := (rows 49 138 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 10 4 8 0 32 64 255), good := (rows 161 138 132 138 128 160 192 128) }] }

theorem profile31_node49 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,136] 6 248 profile31_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,136] 6 248 profile31_node49_cert).mp (by decide +kernel))

def profile31_node50_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 49 146 236 232 248 232 232 128), lower := (rows 49 146 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 19 4 0 16 32 64 255), good := (rows 179 146 132 128 146 160 192 128) }] }

theorem profile31_node50 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,144] 6 232 profile31_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,144] 6 232 profile31_node50_cert).mp (by decide +kernel))

def profile31_node51_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 49 194 188 184 184 184 248 128), lower := (rows 49 194 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 66 4 0 16 32 64 255), good := (rows 177 194 132 128 144 160 194 128) }] }

theorem profile31_node51 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,192] 6 184 profile31_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48,192] 6 184 profile31_node51_cert).mp (by decide +kernel))

def profile31_node40_column : Nat → Fin 8 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile31_node40_route : Route 8 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile31_node40 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [48] 6 (by decide) (choices 2) [24,48,72,80,136,144,192] profile31_node40_route profile31_node40_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node41
  · exact profile31_node42
  · exact profile31_node43
  · exact profile31_node48
  · exact profile31_node49
  · exact profile31_node50
  · exact profile31_node51

def profile31_node54_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 73 26 28 168 176 160 224 128), lower := (rows 73 26 28 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile31_node54 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,24] 6 160 profile31_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,24] 6 160 profile31_node54_cert).mp (by decide +kernel))

def profile31_node56_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 73 26 44 24 176 160 224 128), lower := (rows 73 26 44 24 16 32 64 128), losses := [{ target := 4, region := (rows 15 2 15 8 0 255 255 255), good := (rows 237 239 237 237 224 224 224 224) }] }

theorem profile31_node56 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,40,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,40,16] 6 160 profile31_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,40,16] 6 160 profile31_node56_cert).mp (by decide +kernel))

def profile31_node57_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 73 26 44 40 144 176 208 128), lower := (rows 73 26 44 40 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 44 44 0 32 64 255), good := (rows 205 142 172 172 128 172 192 128) }] }

theorem profile31_node57 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,40,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,40,32] 6 144 profile31_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,40,32] 6 144 profile31_node57_cert).mp (by decide +kernel))

def profile31_node58_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 73 26 44 136 176 176 240 128), lower := (rows 73 26 44 136 16 32 64 128), losses := [{ target := 4, region := (rows 65 2 36 255 0 32 64 255), good := (rows 201 138 172 136 136 172 201 136) }] }

theorem profile31_node58 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,40,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,40,128] 6 176 profile31_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,40,128] 6 176 profile31_node58_cert).mp (by decide +kernel))

def profile31_node55_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile31_node55_route : Route 8 := (fun mask => (mask,id))

theorem profile31_node55 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,40] 6 (by decide) (choices 1) [16,32,128] profile31_node55_route profile31_node55_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node56
  · exact profile31_node57
  · exact profile31_node58

def profile31_node59_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 73 26 52 168 184 168 232 128), lower := (rows 73 26 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile31_node59 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,48] 6 168 profile31_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,48] 6 168 profile31_node59_cert).mp (by decide +kernel))

def profile31_node60_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 73 26 140 184 176 176 240 128), lower := (rows 73 26 140 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 15 8 0 32 64 255), good := (rows 205 142 140 140 128 160 192 128) }] }

theorem profile31_node60 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,136] 6 176 profile31_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,136] 6 176 profile31_node60_cert).mp (by decide +kernel))

def profile31_node61_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 73 26 148 168 184 168 232 128), lower := (rows 73 26 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 22 0 16 32 64 255), good := (rows 193 150 148 128 148 160 192 128) }] }

theorem profile31_node61 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,144] 6 168 profile31_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,144] 6 168 profile31_node61_cert).mp (by decide +kernel))

def profile31_node62_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 73 26 164 184 184 184 248 128), lower := (rows 73 26 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 36 0 16 32 64 255), good := (rows 193 146 164 128 144 164 192 128) }] }

theorem profile31_node62 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,160] 6 184 profile31_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24,160] 6 184 profile31_node62_cert).mp (by decide +kernel))

def profile31_node53_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile31_node53_route : Route 8 := (fun mask => (mask,id))

theorem profile31_node53 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,24] 6 (by decide) (choices 2) [24,40,48,136,144,160] profile31_node53_route profile31_node53_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node54
  · exact profile31_node55
  · exact profile31_node59
  · exact profile31_node60
  · exact profile31_node61
  · exact profile31_node62

def profile31_node64_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 73 50 28 168 184 168 232 128), lower := (rows 73 50 28 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile31_node64 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,24] 6 168 profile31_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,24] 6 168 profile31_node64_cert).mp (by decide +kernel))

def profile31_node65_cert : CutBound 8 := { lost := (rows 0 8 8 0 0 0 0 0), upper := (rows 73 50 52 136 152 168 200 128), lower := (rows 73 50 52 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 6 6 0 16 32 64 255), good := (rows 193 182 182 128 144 160 192 128) }] }

theorem profile31_node65 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,48] 6 136 profile31_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,48] 6 136 profile31_node65_cert).mp (by decide +kernel))

def profile31_node66_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 73 50 140 184 184 184 248 128), lower := (rows 73 50 140 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 13 8 0 32 64 255), good := (rows 205 162 140 140 128 160 192 128) }] }

theorem profile31_node66 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,136] 6 184 profile31_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,136] 6 184 profile31_node66_cert).mp (by decide +kernel))

def profile31_node67_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 73 50 148 168 184 168 232 128), lower := (rows 73 50 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 22 0 16 32 64 255), good := (rows 193 182 148 128 148 160 192 128) }] }

theorem profile31_node67 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,144] 6 168 profile31_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48,144] 6 168 profile31_node67_cert).mp (by decide +kernel))

def profile31_node63_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile31_node63_route : Route 8 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile31_node63 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,48] 6 (by decide) (choices 2) [24,48,136,144] profile31_node63_route profile31_node63_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile31_node64
  · exact profile31_node65
  · exact profile31_node66
  · exact profile31_node67

def profile31_node68_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 73 138 188 184 184 184 248 128), lower := (rows 73 138 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 11 4 8 0 32 64 255), good := (rows 203 138 132 138 128 160 192 128) }] }

theorem profile31_node68 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,136] 6 184 profile31_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,136] 6 184 profile31_node68_cert).mp (by decide +kernel))

def profile31_node69_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 73 146 188 184 184 184 248 128), lower := (rows 73 146 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 18 4 0 16 32 64 255), good := (rows 193 146 132 128 146 160 192 128) }] }

theorem profile31_node69 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,144] 6 184 profile31_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72,144] 6 184 profile31_node69_cert).mp (by decide +kernel))

def profile31_node52_column : Nat → Fin 8 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile31_node52_route : Route 8 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile31_node52 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [72] 6 (by decide) (choices 2) [24,48,136,144] profile31_node52_route profile31_node52_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile31_node53
  · exact profile31_node63
  · exact profile31_node68
  · exact profile31_node69

def profile31_node71_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 81 26 172 168 184 168 232 128), lower := (rows 81 26 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) }] }

theorem profile31_node71 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,24] 6 168 profile31_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,24] 6 168 profile31_node71_cert).mp (by decide +kernel))

def profile31_node73_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 81 42 28 168 184 168 232 128), lower := (rows 81 42 28 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) }] }

theorem profile31_node73 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,24] 6 168 profile31_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,24] 6 168 profile31_node73_cert).mp (by decide +kernel))

def profile31_node74_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 81 42 44 152 152 184 216 128), lower := (rows 81 42 44 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 6 6 8 0 32 64 255), good := (rows 193 174 174 136 128 160 192 128) }] }

theorem profile31_node74 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,40] 6 152 profile31_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,40] 6 152 profile31_node74_cert).mp (by decide +kernel))

def profile31_node75_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 81 42 52 136 152 168 200 128), lower := (rows 81 42 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) }] }

theorem profile31_node75 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,48] 6 136 profile31_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,48] 6 136 profile31_node75_cert).mp (by decide +kernel))

def profile31_node76_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 81 42 140 184 184 184 248 128), lower := (rows 81 42 140 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 14 8 0 32 64 255), good := (rows 193 174 140 140 128 160 192 128) }] }

theorem profile31_node76 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,136] 6 184 profile31_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,136] 6 184 profile31_node76_cert).mp (by decide +kernel))

def profile31_node77_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 81 42 148 168 184 168 232 128), lower := (rows 81 42 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 21 0 16 32 64 255), good := (rows 213 162 148 128 148 160 192 128) }] }

theorem profile31_node77 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,144] 6 168 profile31_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,144] 6 168 profile31_node77_cert).mp (by decide +kernel))

def profile31_node78_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 81 42 164 152 152 184 216 128), lower := (rows 81 42 164 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 38 0 16 32 64 255), good := (rows 209 166 164 128 144 164 192 128) }] }

theorem profile31_node78 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,160] 6 152 profile31_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40,160] 6 152 profile31_node78_cert).mp (by decide +kernel))

def profile31_node72_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile31_node72_route : Route 8 := (fun mask => (mask,id))

theorem profile31_node72 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,40] 6 (by decide) (choices 2) [24,40,48,136,144,160] profile31_node72_route profile31_node72_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node73
  · exact profile31_node74
  · exact profile31_node75
  · exact profile31_node76
  · exact profile31_node77
  · exact profile31_node78

def profile31_node79_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 81 50 172 168 184 168 232 128), lower := (rows 81 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) }] }

theorem profile31_node79 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,48] 6 168 profile31_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,48] 6 168 profile31_node79_cert).mp (by decide +kernel))

def profile31_node80_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 81 138 188 184 184 184 248 128), lower := (rows 81 138 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 10 4 8 0 32 64 255), good := (rows 193 138 132 138 128 160 192 128) }] }

theorem profile31_node80 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,136] 6 184 profile31_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,136] 6 184 profile31_node80_cert).mp (by decide +kernel))

def profile31_node81_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 81 146 172 168 184 168 232 128), lower := (rows 81 146 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 19 4 0 16 32 64 255), good := (rows 211 146 132 128 146 160 192 128) }] }

theorem profile31_node81 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,144] 6 168 profile31_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,144] 6 168 profile31_node81_cert).mp (by decide +kernel))

def profile31_node82_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 81 162 188 184 184 184 248 128), lower := (rows 81 162 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 64 255), good := (rows 209 162 132 128 144 162 192 128) }] }

theorem profile31_node82 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,160] 6 184 profile31_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80,160] 6 184 profile31_node82_cert).mp (by decide +kernel))

def profile31_node70_column : Nat → Fin 8 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 72 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | _ => 0

def profile31_node70_route : Route 8 := (fun mask => (mask,id))

theorem profile31_node70 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [80] 6 (by decide) (choices 2) [24,40,48,136,144,160] profile31_node70_route profile31_node70_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node71
  · exact profile31_node72
  · exact profile31_node79
  · exact profile31_node80
  · exact profile31_node81
  · exact profile31_node82

def profile31_node83_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 137 250 252 248 248 248 248 128), lower := (rows 137 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 9 2 4 8 0 32 64 255), good := (rows 137 130 132 137 128 160 192 128) }] }

theorem profile31_node83 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [136] 6 248 profile31_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [136] 6 248 profile31_node83_cert).mp (by decide +kernel))

def profile31_node84_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 145 250 252 248 248 248 248 128), lower := (rows 145 2 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 17 2 4 0 16 32 64 255), good := (rows 145 130 132 128 145 160 192 128) }] }

theorem profile31_node84 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [144] 6 248 profile31_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [144] 6 248 profile31_node84_cert).mp (by decide +kernel))

def profile31_node85_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 193 186 188 184 184 184 248 128), lower := (rows 193 2 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 65 2 4 0 16 32 64 255), good := (rows 193 130 132 128 144 160 193 128) }] }

theorem profile31_node85 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [192] 6 184 profile31_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [192] 6 184 profile31_node85_cert).mp (by decide +kernel))

def profile31_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile31_node0_route : Route 8 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile31_node0 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [] 6 (by decide) (choices 2) [24,48,72,80,136,144,192] profile31_node0_route profile31_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node1
  · exact profile31_node40
  · exact profile31_node52
  · exact profile31_node70
  · exact profile31_node83
  · exact profile31_node84
  · exact profile31_node85

theorem profile31 : Upper (D (n:=8) [32,32,32,19,18,18,17,2]) (R (n:=8) [32,32,32,19,18,18,17,2]) [] 6 := profile31_node0


#print axioms profile31
end Delivery.SmallBudgetTenFinite8
