import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile29_node2_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 11 11 244 248 240 240 240 128), lower := (rows 11 11 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 247 247 244 244 244 244 244 244) }] }

theorem profile29_node2 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,9] 6 240 profile29_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,9] 6 240 profile29_node2_cert).mp (by decide +kernel))

def profile29_node4_cert : Bound 8 := { allowed := (rows 144 136 128 0 0 0 0 0), upper := (rows 11 19 28 232 240 224 224 128), lower := (rows 11 19 28 8 16 32 64 128), losses := [] }

theorem profile29_node4 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,24] 6 224 profile29_node4_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,24] 6 224 profile29_node4_cert).mp (by decide +kernel))

def profile29_node5_cert : Bound 8 := { allowed := (rows 144 136 144 0 0 0 0 0), upper := (rows 11 19 44 216 208 240 208 128), lower := (rows 11 19 44 8 16 32 64 128), losses := [] }

theorem profile29_node5 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,40] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,40] 6 208 profile29_node5_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,40] 6 208 profile29_node5_cert).mp (by decide +kernel))

def profile29_node6_cert : Bound 8 := { allowed := (rows 144 136 136 0 0 0 0 0), upper := (rows 11 19 52 200 216 232 200 128), lower := (rows 11 19 52 8 16 32 64 128), losses := [] }

theorem profile29_node6 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,48] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,48] 6 200 profile29_node6_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,48] 6 200 profile29_node6_cert).mp (by decide +kernel))

def profile29_node8_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 11 19 100 24 152 168 200 128), lower := (rows 11 19 100 24 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 15 8 0 41 73 255), good := (rows 239 231 228 236 128 160 192 128) }] }

theorem profile29_node8 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,96,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,96,16] 6 136 profile29_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,96,16] 6 136 profile29_node8_cert).mp (by decide +kernel))

def profile29_node9_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 11 19 100 136 152 184 216 128), lower := (rows 11 19 100 136 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 255 0 32 64 255), good := (rows 139 139 236 136 136 168 200 136) }] }

theorem profile29_node9 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,96,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,96,128] 6 152 profile29_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,96,128] 6 152 profile29_node9_cert).mp (by decide +kernel))

def profile29_node7_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node7_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node7 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,96] 6 (by decide) (choices 1) [16,128] profile29_node7_route profile29_node7_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node8
  · exact profile29_node9

def profile29_node10_cert : Bound 8 := { allowed := (rows 144 136 16 0 0 0 0 0), upper := (rows 11 19 140 248 240 240 240 128), lower := (rows 11 19 140 8 16 32 64 128), losses := [] }

theorem profile29_node10 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,136] 6 240 profile29_node10_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,136] 6 240 profile29_node10_cert).mp (by decide +kernel))

def profile29_node11_cert : Bound 8 := { allowed := (rows 144 136 8 0 0 0 0 0), upper := (rows 11 19 148 232 248 232 232 128), lower := (rows 11 19 148 8 16 32 64 128), losses := [] }

theorem profile29_node11 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,144] 6 232 profile29_node11_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,144] 6 232 profile29_node11_cert).mp (by decide +kernel))

def profile29_node12_cert : Bound 8 := { allowed := (rows 144 136 24 0 0 0 0 0), upper := (rows 11 19 164 216 216 248 216 128), lower := (rows 11 19 164 8 16 32 64 128), losses := [] }

theorem profile29_node12 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,160] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,160] 6 216 profile29_node12_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17,160] 6 216 profile29_node12_cert).mp (by decide +kernel))

def profile29_node3_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | _ => 0

def profile29_node3_route : Route 8 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile29_node3 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,17] 6 (by decide) (choices 2) [24,40,48,96,136,144,160] profile29_node3_route profile29_node3_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node4
  · exact profile29_node5
  · exact profile29_node6
  · exact profile29_node7
  · exact profile29_node10
  · exact profile29_node11
  · exact profile29_node12

def profile29_node13_cert : Bound 8 := { allowed := (rows 144 128 152 0 0 0 0 0), upper := (rows 11 26 245 249 241 241 241 128), lower := (rows 11 26 4 8 16 32 64 128), losses := [] }

theorem profile29_node13 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,24] 6 241 profile29_node13_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,24] 6 241 profile29_node13_cert).mp (by decide +kernel))

def profile29_node15_cert : Bound 8 := { allowed := (rows 144 152 128 0 0 0 0 0), upper := (rows 11 35 28 216 208 240 208 128), lower := (rows 11 35 28 8 16 32 64 128), losses := [] }

theorem profile29_node15 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,24] 6 208 profile29_node15_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,24] 6 208 profile29_node15_cert).mp (by decide +kernel))

def profile29_node16_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 11 35 76 152 144 176 208 128), lower := (rows 11 35 76 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) }] }

theorem profile29_node16 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,72] 6 144 profile29_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,72] 6 144 profile29_node16_cert).mp (by decide +kernel))

def profile29_node18_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 11 35 84 24 152 168 200 128), lower := (rows 11 35 84 24 16 32 64 128), losses := [{ target := 4, region := (rows 9 11 4 8 0 41 73 255), good := (rows 235 227 196 235 128 160 192 128) }] }

theorem profile29_node18 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,80,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,80,16] 6 136 profile29_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,80,16] 6 136 profile29_node18_cert).mp (by decide +kernel))

def profile29_node19_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 11 35 84 136 152 184 216 128), lower := (rows 11 35 84 136 16 32 64 128), losses := [{ target := 4, region := (rows 35 34 4 255 0 32 64 255), good := (rows 139 171 204 136 136 171 200 136) }] }

theorem profile29_node19 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,80,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,80,128] 6 152 profile29_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,80,128] 6 152 profile29_node19_cert).mp (by decide +kernel))

def profile29_node17_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node17_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node17 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,80] 6 (by decide) (choices 1) [16,128] profile29_node17_route profile29_node17_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node18
  · exact profile29_node19

def profile29_node20_cert : Bound 8 := { allowed := (rows 144 152 16 0 0 0 0 0), upper := (rows 11 35 140 216 208 240 208 128), lower := (rows 11 35 140 8 16 32 64 128), losses := [] }

theorem profile29_node20 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,136] 6 208 profile29_node20_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,136] 6 208 profile29_node20_cert).mp (by decide +kernel))

def profile29_node21_cert : Bound 8 := { allowed := (rows 144 152 8 0 0 0 0 0), upper := (rows 11 35 148 216 216 248 216 128), lower := (rows 11 35 148 8 16 32 64 128), losses := [] }

theorem profile29_node21 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,144] 6 216 profile29_node21_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,144] 6 216 profile29_node21_cert).mp (by decide +kernel))

def profile29_node22_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 11 35 196 152 152 184 216 128), lower := (rows 11 35 196 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 68 0 16 32 64 255), good := (rows 131 163 196 128 144 160 196 128) }] }

theorem profile29_node22 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,192] 6 152 profile29_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33,192] 6 152 profile29_node22_cert).mp (by decide +kernel))

def profile29_node14_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile29_node14_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node14 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,33] 6 (by decide) (choices 2) [24,72,80,136,144,192] profile29_node14_route profile29_node14_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node15
  · exact profile29_node16
  · exact profile29_node17
  · exact profile29_node20
  · exact profile29_node21
  · exact profile29_node22

def profile29_node23_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 11 42 213 217 209 241 209 128), lower := (rows 11 42 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 255), good := (rows 247 162 132 128 144 160 192 128) }] }

theorem profile29_node23 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,40] 6 209 profile29_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,40] 6 209 profile29_node23_cert).mp (by decide +kernel))

def profile29_node25_cert : Bound 8 := { allowed := (rows 144 136 144 0 0 0 0 0), upper := (rows 11 50 13 216 208 240 208 128), lower := (rows 11 50 13 8 16 32 64 128), losses := [] }

theorem profile29_node25 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,9] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,9] 6 208 profile29_node25_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,9] 6 208 profile29_node25_cert).mp (by decide +kernel))

def profile29_node26_cert : Bound 8 := { allowed := (rows 144 136 136 0 0 0 0 0), upper := (rows 11 50 21 200 216 232 200 128), lower := (rows 11 50 21 8 16 32 64 128), losses := [] }

theorem profile29_node26 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,17] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,17] 6 200 profile29_node26_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,17] 6 200 profile29_node26_cert).mp (by decide +kernel))

def profile29_node27_cert : Bound 8 := { allowed := (rows 144 136 128 0 0 0 0 0), upper := (rows 11 50 28 201 209 225 193 128), lower := (rows 11 50 28 8 16 32 64 128), losses := [] }

theorem profile29_node27 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,24] 6 193 profile29_node27_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,24] 6 193 profile29_node27_cert).mp (by decide +kernel))

def profile29_node29_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 11 50 69 24 152 168 200 128), lower := (rows 11 50 69 24 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 41 73 255), good := (rows 239 162 229 232 128 160 192 128) }] }

theorem profile29_node29 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,65,16] 6 136 profile29_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,65,16] 6 136 profile29_node29_cert).mp (by decide +kernel))

def profile29_node30_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 11 50 69 136 152 184 216 128), lower := (rows 11 50 69 136 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 255 0 32 64 255), good := (rows 139 171 205 136 136 168 200 136) }] }

theorem profile29_node30 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,65,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,65,128] 6 152 profile29_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,65,128] 6 152 profile29_node30_cert).mp (by decide +kernel))

def profile29_node28_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node28_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node28 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,65] 6 (by decide) (choices 1) [16,128] profile29_node28_route profile29_node28_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node29
  · exact profile29_node30

def profile29_node31_cert : Bound 8 := { allowed := (rows 144 136 144 0 0 0 0 0), upper := (rows 11 50 76 153 145 177 209 128), lower := (rows 11 50 76 8 16 32 64 128), losses := [] }

theorem profile29_node31 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,72] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,72] 6 145 profile29_node31_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,72] 6 145 profile29_node31_cert).mp (by decide +kernel))

def profile29_node32_cert : Bound 8 := { allowed := (rows 144 136 136 0 0 0 0 0), upper := (rows 11 50 84 137 153 169 201 128), lower := (rows 11 50 84 8 16 32 64 128), losses := [] }

theorem profile29_node32 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,80] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,80] 6 137 profile29_node32_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,80] 6 137 profile29_node32_cert).mp (by decide +kernel))

def profile29_node33_cert : Bound 8 := { allowed := (rows 144 136 24 0 0 0 0 0), upper := (rows 11 50 133 216 216 248 216 128), lower := (rows 11 50 133 8 16 32 64 128), losses := [] }

theorem profile29_node33 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,129] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,129] 6 216 profile29_node33_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,129] 6 216 profile29_node33_cert).mp (by decide +kernel))

def profile29_node34_cert : Bound 8 := { allowed := (rows 144 136 16 0 0 0 0 0), upper := (rows 11 50 140 217 209 241 209 128), lower := (rows 11 50 140 8 16 32 64 128), losses := [] }

theorem profile29_node34 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,136] 6 209 profile29_node34_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,136] 6 209 profile29_node34_cert).mp (by decide +kernel))

def profile29_node35_cert : Bound 8 := { allowed := (rows 144 136 8 0 0 0 0 0), upper := (rows 11 50 148 201 217 233 201 128), lower := (rows 11 50 148 8 16 32 64 128), losses := [] }

theorem profile29_node35 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,144] 6 201 profile29_node35_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,144] 6 201 profile29_node35_cert).mp (by decide +kernel))

def profile29_node36_cert : Bound 8 := { allowed := (rows 144 136 24 0 0 0 0 0), upper := (rows 11 50 196 153 153 185 217 128), lower := (rows 11 50 196 8 16 32 64 128), losses := [] }

theorem profile29_node36 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,192] 6 153 profile29_node36_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48,192] 6 153 profile29_node36_cert).mp (by decide +kernel))

def profile29_node24_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile29_node24_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node24 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,48] 6 (by decide) (choices 2) [9,17,24,65,72,80,129,136,144,192] profile29_node24_route profile29_node24_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node25
  · exact profile29_node26
  · exact profile29_node27
  · exact profile29_node28
  · exact profile29_node31
  · exact profile29_node32
  · exact profile29_node33
  · exact profile29_node34
  · exact profile29_node35
  · exact profile29_node36

def profile29_node38_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 11 98 13 152 144 176 208 128), lower := (rows 11 98 13 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 255 4 0 255 255 255 255), good := (rows 243 242 247 242 242 242 242 242) }] }

theorem profile29_node38 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,9] 6 144 profile29_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,9] 6 144 profile29_node38_cert).mp (by decide +kernel))

def profile29_node40_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 11 98 21 24 152 168 200 128), lower := (rows 11 98 21 24 16 32 64 128), losses := [{ target := 4, region := (rows 9 15 4 8 0 41 73 255), good := (rows 235 226 231 235 128 160 192 128) }] }

theorem profile29_node40 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,17,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,17,16] 6 136 profile29_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,17,16] 6 136 profile29_node40_cert).mp (by decide +kernel))

def profile29_node41_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 11 98 21 136 152 184 216 128), lower := (rows 11 98 21 136 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 255 0 32 64 255), good := (rows 139 235 141 136 136 168 200 136) }] }

theorem profile29_node41 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,17,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,17,128] 6 152 profile29_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,17,128] 6 152 profile29_node41_cert).mp (by decide +kernel))

def profile29_node39_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node39_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node39 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,17] 6 (by decide) (choices 1) [16,128] profile29_node39_route profile29_node39_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node40
  · exact profile29_node41

def profile29_node42_cert : Bound 8 := { allowed := (rows 144 152 128 0 0 0 0 0), upper := (rows 11 98 28 153 145 177 209 128), lower := (rows 11 98 28 8 16 32 64 128), losses := [] }

theorem profile29_node42 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,24] 6 145 profile29_node42_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,24] 6 145 profile29_node42_cert).mp (by decide +kernel))

def profile29_node43_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 11 98 133 152 152 184 216 128), lower := (rows 11 98 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64 255), good := (rows 135 226 133 128 144 160 192 128) }] }

theorem profile29_node43 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,129] 6 152 profile29_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,129] 6 152 profile29_node43_cert).mp (by decide +kernel))

def profile29_node44_cert : Bound 8 := { allowed := (rows 144 152 16 0 0 0 0 0), upper := (rows 11 98 140 153 145 177 209 128), lower := (rows 11 98 140 8 16 32 64 128), losses := [] }

theorem profile29_node44 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,136] 6 145 profile29_node44_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,136] 6 145 profile29_node44_cert).mp (by decide +kernel))

def profile29_node45_cert : Bound 8 := { allowed := (rows 144 152 8 0 0 0 0 0), upper := (rows 11 98 148 153 153 185 217 128), lower := (rows 11 98 148 8 16 32 64 128), losses := [] }

theorem profile29_node45 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,144] 6 153 profile29_node45_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96,144] 6 153 profile29_node45_cert).mp (by decide +kernel))

def profile29_node37_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile29_node37_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node37 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,96] 6 (by decide) (choices 2) [9,17,24,129,136,144] profile29_node37_route profile29_node37_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node38
  · exact profile29_node39
  · exact profile29_node42
  · exact profile29_node43
  · exact profile29_node44
  · exact profile29_node45

def profile29_node46_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 11 131 252 248 248 248 248 128), lower := (rows 11 131 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64 255), good := (rows 131 131 132 128 144 160 192 128) }] }

theorem profile29_node46 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,129] 6 248 profile29_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,129] 6 248 profile29_node46_cert).mp (by decide +kernel))

def profile29_node47_cert : Bound 8 := { allowed := (rows 144 16 152 0 0 0 0 0), upper := (rows 11 138 245 249 241 241 241 128), lower := (rows 11 138 4 8 16 32 64 128), losses := [] }

theorem profile29_node47 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,136] 6 241 profile29_node47_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,136] 6 241 profile29_node47_cert).mp (by decide +kernel))

def profile29_node48_cert : Bound 8 := { allowed := (rows 144 8 152 0 0 0 0 0), upper := (rows 11 146 253 249 249 249 249 128), lower := (rows 11 146 4 8 16 32 64 128), losses := [] }

theorem profile29_node48 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,144] 6 249 profile29_node48_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,144] 6 249 profile29_node48_cert).mp (by decide +kernel))

def profile29_node49_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 11 162 221 217 217 249 217 128), lower := (rows 11 162 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 64 255), good := (rows 131 162 132 128 144 162 192 128) }] }

theorem profile29_node49 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,160] 6 217 profile29_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10,160] 6 217 profile29_node49_cert).mp (by decide +kernel))

def profile29_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile29_node1_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile29_node1 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [10] 6 (by decide) (choices 2) [9,17,24,33,40,48,96,129,136,144,160] profile29_node1_route profile29_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node2
  · exact profile29_node3
  · exact profile29_node13
  · exact profile29_node14
  · exact profile29_node23
  · exact profile29_node24
  · exact profile29_node37
  · exact profile29_node46
  · exact profile29_node47
  · exact profile29_node48
  · exact profile29_node49

def profile29_node51_cert : Bound 8 := { allowed := (rows 128 144 152 0 0 0 0 0), upper := (rows 25 11 246 250 242 242 242 128), lower := (rows 25 11 4 8 16 32 64 128), losses := [] }

theorem profile29_node51 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,9] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,9] 6 242 profile29_node51_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,9] 6 242 profile29_node51_cert).mp (by decide +kernel))

def profile29_node52_cert : Bound 8 := { allowed := (rows 128 128 152 0 0 0 0 0), upper := (rows 25 26 231 235 243 227 227 128), lower := (rows 25 26 4 8 16 32 64 128), losses := [] }

theorem profile29_node52 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,24] 6 227 profile29_node52_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,24] 6 227 profile29_node52_cert).mp (by decide +kernel))

def profile29_node54_cert : Bound 8 := { allowed := (rows 128 152 144 0 0 0 0 0), upper := (rows 25 35 14 216 208 240 208 128), lower := (rows 25 35 14 8 16 32 64 128), losses := [] }

theorem profile29_node54 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,10] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,10] 6 208 profile29_node54_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,10] 6 208 profile29_node54_cert).mp (by decide +kernel))

def profile29_node55_cert : Bound 8 := { allowed := (rows 128 152 128 0 0 0 0 0), upper := (rows 25 35 28 202 210 226 194 128), lower := (rows 25 35 28 8 16 32 64 128), losses := [] }

theorem profile29_node55 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,24] 6 194 profile29_node55_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,24] 6 194 profile29_node55_cert).mp (by decide +kernel))

def profile29_node57_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 25 35 70 24 152 168 200 128), lower := (rows 25 35 70 24 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 7 8 0 41 73 255), good := (rows 239 231 198 232 128 160 192 128) }] }

theorem profile29_node57 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66,16] 6 136 profile29_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66,16] 6 136 profile29_node57_cert).mp (by decide +kernel))

def profile29_node59_cert : CutBound 8 := { lost := (rows 0 8 8 0 0 0 0 0), upper := (rows 25 35 70 136 24 176 208 128), lower := (rows 25 35 70 136 24 32 64 128), losses := [{ target := 3, region := (rows 1 3 7 0 16 49 81 255), good := (rows 247 231 198 128 240 160 192 128) }] }

theorem profile29_node59 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66,128,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66,128,8] 6 144 profile29_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66,128,8] 6 144 profile29_node59_cert).mp (by decide +kernel))

def profile29_node60_cert : CutBound 8 := { lost := (rows 0 128 128 0 0 0 0 0), upper := (rows 25 35 70 136 144 56 88 128), lower := (rows 25 35 70 136 144 32 64 128), losses := [{ target := 7, region := (rows 1 3 7 8 16 33 65 0), good := (rows 127 103 70 8 16 32 64 0) }] }

theorem profile29_node60 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66,128,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66,128,128] 6 24 profile29_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66,128,128] 6 24 profile29_node60_cert).mp (by decide +kernel))

def profile29_node58_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node58_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node58 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66,128] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66,128] 6 (by decide) (choices 1) [8,128] profile29_node58_route profile29_node58_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node59
  · exact profile29_node60

def profile29_node56_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node56_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node56 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,66] 6 (by decide) (choices 1) [16,128] profile29_node56_route profile29_node56_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node57
  · exact profile29_node58

def profile29_node61_cert : Bound 8 := { allowed := (rows 128 152 144 0 0 0 0 0), upper := (rows 25 35 76 154 146 178 210 128), lower := (rows 25 35 76 8 16 32 64 128), losses := [] }

theorem profile29_node61 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,72] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,72] 6 146 profile29_node61_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,72] 6 146 profile29_node61_cert).mp (by decide +kernel))

def profile29_node62_cert : Bound 8 := { allowed := (rows 128 152 24 0 0 0 0 0), upper := (rows 25 35 134 216 216 248 216 128), lower := (rows 25 35 134 8 16 32 64 128), losses := [] }

theorem profile29_node62 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,130] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,130] 6 216 profile29_node62_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,130] 6 216 profile29_node62_cert).mp (by decide +kernel))

def profile29_node63_cert : Bound 8 := { allowed := (rows 128 152 16 0 0 0 0 0), upper := (rows 25 35 140 218 210 242 210 128), lower := (rows 25 35 140 8 16 32 64 128), losses := [] }

theorem profile29_node63 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,136] 6 210 profile29_node63_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,136] 6 210 profile29_node63_cert).mp (by decide +kernel))

def profile29_node64_cert : Bound 8 := { allowed := (rows 128 152 24 0 0 0 0 0), upper := (rows 25 35 196 154 154 186 218 128), lower := (rows 25 35 196 8 16 32 64 128), losses := [] }

theorem profile29_node64 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,192] 6 154 profile29_node64_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33,192] 6 154 profile29_node64_cert).mp (by decide +kernel))

def profile29_node53_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 34 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile29_node53_route : Route 8 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node53 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,33] 6 (by decide) (choices 2) [10,24,66,72,130,136,192] profile29_node53_route profile29_node53_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node54
  · exact profile29_node55
  · exact profile29_node56
  · exact profile29_node61
  · exact profile29_node62
  · exact profile29_node63
  · exact profile29_node64

def profile29_node65_cert : Bound 8 := { allowed := (rows 128 144 152 0 0 0 0 0), upper := (rows 25 42 215 219 211 243 211 128), lower := (rows 25 42 4 8 16 32 64 128), losses := [] }

theorem profile29_node65 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,40] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,40] 6 211 profile29_node65_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,40] 6 211 profile29_node65_cert).mp (by decide +kernel))

def profile29_node68_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 25 98 7 24 152 168 200 128), lower := (rows 25 98 7 24 16 32 64 128), losses := [{ target := 4, region := (rows 1 15 5 8 0 41 73 255), good := (rows 239 226 231 234 128 160 192 128) }] }

theorem profile29_node68 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3,16] 6 136 profile29_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3,16] 6 136 profile29_node68_cert).mp (by decide +kernel))

def profile29_node70_cert : CutBound 8 := { lost := (rows 0 8 8 0 0 0 0 0), upper := (rows 25 98 7 136 24 176 208 128), lower := (rows 25 98 7 136 24 32 64 128), losses := [{ target := 3, region := (rows 1 23 5 0 16 49 81 255), good := (rows 247 226 231 128 242 160 192 128) }] }

theorem profile29_node70 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3,128,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3,128,8] 6 144 profile29_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3,128,8] 6 144 profile29_node70_cert).mp (by decide +kernel))

def profile29_node71_cert : CutBound 8 := { lost := (rows 0 128 128 0 0 0 0 0), upper := (rows 25 98 7 136 144 56 88 128), lower := (rows 25 98 7 136 144 32 64 128), losses := [{ target := 7, region := (rows 1 7 5 8 16 33 65 0), good := (rows 127 98 103 8 16 32 64 0) }] }

theorem profile29_node71 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3,128,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3,128,128] 6 24 profile29_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3,128,128] 6 24 profile29_node71_cert).mp (by decide +kernel))

def profile29_node69_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node69_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node69 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3,128] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3,128] 6 (by decide) (choices 1) [8,128] profile29_node69_route profile29_node69_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node70
  · exact profile29_node71

def profile29_node67_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node67_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node67 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,3] 6 (by decide) (choices 1) [16,128] profile29_node67_route profile29_node67_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node68
  · exact profile29_node69

def profile29_node72_cert : Bound 8 := { allowed := (rows 128 152 144 0 0 0 0 0), upper := (rows 25 98 13 154 146 178 210 128), lower := (rows 25 98 13 8 16 32 64 128), losses := [] }

theorem profile29_node72 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,9] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,9] 6 146 profile29_node72_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,9] 6 146 profile29_node72_cert).mp (by decide +kernel))

def profile29_node73_cert : Bound 8 := { allowed := (rows 128 152 144 0 0 0 0 0), upper := (rows 25 98 14 153 145 177 209 128), lower := (rows 25 98 14 8 16 32 64 128), losses := [] }

theorem profile29_node73 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,10] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,10] 6 145 profile29_node73_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,10] 6 145 profile29_node73_cert).mp (by decide +kernel))

def profile29_node74_cert : Bound 8 := { allowed := (rows 128 152 128 0 0 0 0 0), upper := (rows 25 98 28 139 147 163 195 128), lower := (rows 25 98 28 8 16 32 64 128), losses := [] }

theorem profile29_node74 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,24] 6 131 profile29_node74_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,24] 6 131 profile29_node74_cert).mp (by decide +kernel))

def profile29_node75_cert : Bound 8 := { allowed := (rows 128 152 24 0 0 0 0 0), upper := (rows 25 98 133 154 154 186 218 128), lower := (rows 25 98 133 8 16 32 64 128), losses := [] }

theorem profile29_node75 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,129] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,129] 6 154 profile29_node75_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,129] 6 154 profile29_node75_cert).mp (by decide +kernel))

def profile29_node76_cert : Bound 8 := { allowed := (rows 128 152 24 0 0 0 0 0), upper := (rows 25 98 134 153 153 185 217 128), lower := (rows 25 98 134 8 16 32 64 128), losses := [] }

theorem profile29_node76 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,130] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,130] 6 153 profile29_node76_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,130] 6 153 profile29_node76_cert).mp (by decide +kernel))

def profile29_node77_cert : Bound 8 := { allowed := (rows 128 152 16 0 0 0 0 0), upper := (rows 25 98 140 155 147 179 211 128), lower := (rows 25 98 140 8 16 32 64 128), losses := [] }

theorem profile29_node77 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,136] 6 147 profile29_node77_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96,136] 6 147 profile29_node77_cert).mp (by decide +kernel))

def profile29_node66_column : Nat → Fin 8 := fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile29_node66_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node66 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,96] 6 (by decide) (choices 2) [3,9,10,24,129,130,136] profile29_node66_route profile29_node66_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node67
  · exact profile29_node72
  · exact profile29_node73
  · exact profile29_node74
  · exact profile29_node75
  · exact profile29_node76
  · exact profile29_node77

def profile29_node78_cert : Bound 8 := { allowed := (rows 128 24 152 0 0 0 0 0), upper := (rows 25 131 254 250 250 250 250 128), lower := (rows 25 131 4 8 16 32 64 128), losses := [] }

theorem profile29_node78 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,129] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,129] 6 250 profile29_node78_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,129] 6 250 profile29_node78_cert).mp (by decide +kernel))

def profile29_node79_cert : Bound 8 := { allowed := (rows 128 16 152 0 0 0 0 0), upper := (rows 25 138 247 251 243 243 243 128), lower := (rows 25 138 4 8 16 32 64 128), losses := [] }

theorem profile29_node79 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,136] 6 243 profile29_node79_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,136] 6 243 profile29_node79_cert).mp (by decide +kernel))

def profile29_node80_cert : Bound 8 := { allowed := (rows 128 24 152 0 0 0 0 0), upper := (rows 25 162 223 219 219 251 219 128), lower := (rows 25 162 4 8 16 32 64 128), losses := [] }

theorem profile29_node80 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,160] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,160] 6 219 profile29_node80_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24,160] 6 219 profile29_node80_cert).mp (by decide +kernel))

def profile29_node50_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile29_node50_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile29_node50 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [24] 6 (by decide) (choices 2) [9,24,33,40,96,129,136,160] profile29_node50_route profile29_node50_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node51
  · exact profile29_node52
  · exact profile29_node53
  · exact profile29_node65
  · exact profile29_node66
  · exact profile29_node78
  · exact profile29_node79
  · exact profile29_node80

def profile29_node83_cert : Bound 8 := { allowed := (rows 152 144 128 0 0 0 0 0), upper := (rows 35 11 28 216 208 240 208 128), lower := (rows 35 11 28 8 16 32 64 128), losses := [] }

theorem profile29_node83 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,24] 6 208 profile29_node83_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,24] 6 208 profile29_node83_cert).mp (by decide +kernel))

def profile29_node84_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 35 11 76 152 144 176 208 128), lower := (rows 35 11 76 8 16 32 64 128), losses := [{ target := 3, region := (rows 3 2 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) }] }

theorem profile29_node84 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,72] 6 144 profile29_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,72] 6 144 profile29_node84_cert).mp (by decide +kernel))

def profile29_node86_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 35 11 84 24 152 168 200 128), lower := (rows 35 11 84 24 16 32 64 128), losses := [{ target := 4, region := (rows 11 10 4 8 0 42 74 255), good := (rows 227 235 196 235 128 160 192 128) }] }

theorem profile29_node86 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,80,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,80,16] 6 136 profile29_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,80,16] 6 136 profile29_node86_cert).mp (by decide +kernel))

def profile29_node87_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 35 11 84 136 152 184 216 128), lower := (rows 35 11 84 136 16 32 64 128), losses := [{ target := 4, region := (rows 33 35 4 255 0 32 64 255), good := (rows 171 139 204 136 136 171 200 136) }] }

theorem profile29_node87 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,80,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,80,128] 6 152 profile29_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,80,128] 6 152 profile29_node87_cert).mp (by decide +kernel))

def profile29_node85_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node85_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node85 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,80] 6 (by decide) (choices 1) [16,128] profile29_node85_route profile29_node85_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node86
  · exact profile29_node87

def profile29_node88_cert : Bound 8 := { allowed := (rows 152 144 16 0 0 0 0 0), upper := (rows 35 11 140 216 208 240 208 128), lower := (rows 35 11 140 8 16 32 64 128), losses := [] }

theorem profile29_node88 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,136] 6 208 profile29_node88_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,136] 6 208 profile29_node88_cert).mp (by decide +kernel))

def profile29_node89_cert : Bound 8 := { allowed := (rows 152 144 8 0 0 0 0 0), upper := (rows 35 11 148 216 216 248 216 128), lower := (rows 35 11 148 8 16 32 64 128), losses := [] }

theorem profile29_node89 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,144] 6 216 profile29_node89_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,144] 6 216 profile29_node89_cert).mp (by decide +kernel))

def profile29_node90_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 35 11 196 152 152 184 216 128), lower := (rows 35 11 196 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 68 0 16 32 64 255), good := (rows 163 131 196 128 144 160 196 128) }] }

theorem profile29_node90 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,192] 6 152 profile29_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9,192] 6 152 profile29_node90_cert).mp (by decide +kernel))

def profile29_node82_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile29_node82_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node82 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,9] 6 (by decide) (choices 2) [24,72,80,136,144,192] profile29_node82_route profile29_node82_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node83
  · exact profile29_node84
  · exact profile29_node85
  · exact profile29_node88
  · exact profile29_node89
  · exact profile29_node90

def profile29_node92_cert : Bound 8 := { allowed := (rows 152 128 144 0 0 0 0 0), upper := (rows 35 26 13 216 208 240 208 128), lower := (rows 35 26 13 8 16 32 64 128), losses := [] }

theorem profile29_node92 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,9] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,9] 6 208 profile29_node92_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,9] 6 208 profile29_node92_cert).mp (by decide +kernel))

def profile29_node93_cert : Bound 8 := { allowed := (rows 152 128 128 0 0 0 0 0), upper := (rows 35 26 28 201 209 225 193 128), lower := (rows 35 26 28 8 16 32 64 128), losses := [] }

theorem profile29_node93 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,24] 6 193 profile29_node93_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,24] 6 193 profile29_node93_cert).mp (by decide +kernel))

def profile29_node95_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 35 26 69 24 152 168 200 128), lower := (rows 35 26 69 24 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 7 8 0 42 74 255), good := (rows 231 239 197 232 128 160 192 128) }] }

theorem profile29_node95 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65,16] 6 136 profile29_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65,16] 6 136 profile29_node95_cert).mp (by decide +kernel))

def profile29_node97_cert : CutBound 8 := { lost := (rows 8 0 8 0 0 0 0 0), upper := (rows 35 26 69 136 24 176 208 128), lower := (rows 35 26 69 136 24 32 64 128), losses := [{ target := 3, region := (rows 3 2 7 0 16 50 82 255), good := (rows 231 247 197 128 240 160 192 128) }] }

theorem profile29_node97 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65,128,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65,128,8] 6 144 profile29_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65,128,8] 6 144 profile29_node97_cert).mp (by decide +kernel))

def profile29_node98_cert : CutBound 8 := { lost := (rows 128 0 128 0 0 0 0 0), upper := (rows 35 26 69 136 144 56 88 128), lower := (rows 35 26 69 136 144 32 64 128), losses := [{ target := 7, region := (rows 3 2 7 8 16 34 66 0), good := (rows 103 127 69 8 16 32 64 0) }] }

theorem profile29_node98 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65,128,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65,128,128] 6 24 profile29_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65,128,128] 6 24 profile29_node98_cert).mp (by decide +kernel))

def profile29_node96_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node96_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node96 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65,128] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65,128] 6 (by decide) (choices 1) [8,128] profile29_node96_route profile29_node96_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node97
  · exact profile29_node98

def profile29_node94_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node94_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node94 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,65] 6 (by decide) (choices 1) [16,128] profile29_node94_route profile29_node94_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node95
  · exact profile29_node96

def profile29_node99_cert : Bound 8 := { allowed := (rows 152 128 144 0 0 0 0 0), upper := (rows 35 26 76 153 145 177 209 128), lower := (rows 35 26 76 8 16 32 64 128), losses := [] }

theorem profile29_node99 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,72] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,72] 6 145 profile29_node99_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,72] 6 145 profile29_node99_cert).mp (by decide +kernel))

def profile29_node100_cert : Bound 8 := { allowed := (rows 152 128 24 0 0 0 0 0), upper := (rows 35 26 133 216 216 248 216 128), lower := (rows 35 26 133 8 16 32 64 128), losses := [] }

theorem profile29_node100 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,129] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,129] 6 216 profile29_node100_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,129] 6 216 profile29_node100_cert).mp (by decide +kernel))

def profile29_node101_cert : Bound 8 := { allowed := (rows 152 128 16 0 0 0 0 0), upper := (rows 35 26 140 217 209 241 209 128), lower := (rows 35 26 140 8 16 32 64 128), losses := [] }

theorem profile29_node101 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,136] 6 209 profile29_node101_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,136] 6 209 profile29_node101_cert).mp (by decide +kernel))

def profile29_node102_cert : Bound 8 := { allowed := (rows 152 128 24 0 0 0 0 0), upper := (rows 35 26 196 153 153 185 217 128), lower := (rows 35 26 196 8 16 32 64 128), losses := [] }

theorem profile29_node102 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,192] 6 153 profile29_node102_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24,192] 6 153 profile29_node102_cert).mp (by decide +kernel))

def profile29_node91_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile29_node91_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node91 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,24] 6 (by decide) (choices 2) [9,24,65,72,129,136,192] profile29_node91_route profile29_node91_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node92
  · exact profile29_node93
  · exact profile29_node94
  · exact profile29_node99
  · exact profile29_node100
  · exact profile29_node101
  · exact profile29_node102

def profile29_node105_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 35 67 28 24 152 168 200 128), lower := (rows 35 67 28 24 16 32 64 128), losses := [{ target := 4, region := (rows 13 14 4 8 0 44 76 255), good := (rows 163 195 239 235 128 160 192 128) }] }

theorem profile29_node105 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24,16] 6 136 profile29_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24,16] 6 136 profile29_node105_cert).mp (by decide +kernel))

def profile29_node107_cert : CutBound 8 := { lost := (rows 8 8 0 0 0 0 0 0), upper := (rows 35 67 28 136 24 176 208 128), lower := (rows 35 67 28 136 24 32 64 128), losses := [{ target := 3, region := (rows 21 22 4 0 16 52 84 255), good := (rows 163 195 247 128 243 160 192 128) }] }

theorem profile29_node107 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24,128,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24,128,8] 6 144 profile29_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24,128,8] 6 144 profile29_node107_cert).mp (by decide +kernel))

def profile29_node108_cert : CutBound 8 := { lost := (rows 128 128 0 0 0 0 0 0), upper := (rows 35 67 28 136 144 56 88 128), lower := (rows 35 67 28 136 144 32 64 128), losses := [{ target := 7, region := (rows 5 6 4 8 16 36 68 0), good := (rows 35 67 127 8 16 32 64 0) }] }

theorem profile29_node108 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24,128,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24,128,128] 6 24 profile29_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24,128,128] 6 24 profile29_node108_cert).mp (by decide +kernel))

def profile29_node106_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node106_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node106 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24,128] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24,128] 6 (by decide) (choices 1) [8,128] profile29_node106_route profile29_node106_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node107
  · exact profile29_node108

def profile29_node104_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node104_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node104 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,24] 6 (by decide) (choices 1) [16,128] profile29_node104_route profile29_node104_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node105
  · exact profile29_node106

def profile29_node109_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 35 67 140 152 152 184 216 128), lower := (rows 35 67 140 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 64 255), good := (rows 163 195 140 140 128 160 192 128) }] }

theorem profile29_node109 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,136] 6 152 profile29_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65,136] 6 152 profile29_node109_cert).mp (by decide +kernel))

def profile29_node103_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile29_node103_route : Route 8 := (fun mask => match mask with | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node103 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,65] 6 (by decide) (choices 2) [24,136] profile29_node103_route profile29_node103_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node104
  · exact profile29_node109

def profile29_node111_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 35 74 13 152 144 176 208 128), lower := (rows 35 74 13 8 16 32 64 128), losses := [{ target := 3, region := (rows 3 2 4 0 255 255 255 255), good := (rows 243 243 245 240 240 240 240 240) }] }

theorem profile29_node111 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,9] 6 144 profile29_node111_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,9] 6 144 profile29_node111_cert).mp (by decide +kernel))

def profile29_node113_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 35 74 21 24 152 168 200 128), lower := (rows 35 74 21 24 16 32 64 128), losses := [{ target := 4, region := (rows 11 10 4 8 0 42 74 255), good := (rows 227 235 133 235 128 160 192 128) }] }

theorem profile29_node113 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,17,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,17,16] 6 136 profile29_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,17,16] 6 136 profile29_node113_cert).mp (by decide +kernel))

def profile29_node114_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 35 74 21 136 152 184 216 128), lower := (rows 35 74 21 136 16 32 64 128), losses := [{ target := 4, region := (rows 1 66 4 255 0 32 64 255), good := (rows 171 202 141 136 136 168 202 136) }] }

theorem profile29_node114 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,17,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,17,128] 6 152 profile29_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,17,128] 6 152 profile29_node114_cert).mp (by decide +kernel))

def profile29_node112_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node112_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node112 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,17] 6 (by decide) (choices 1) [16,128] profile29_node112_route profile29_node112_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node113
  · exact profile29_node114

def profile29_node115_cert : Bound 8 := { allowed := (rows 152 144 128 0 0 0 0 0), upper := (rows 35 74 28 153 145 177 209 128), lower := (rows 35 74 28 8 16 32 64 128), losses := [] }

theorem profile29_node115 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,24] 6 145 profile29_node115_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,24] 6 145 profile29_node115_cert).mp (by decide +kernel))

def profile29_node116_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 35 74 133 152 152 184 216 128), lower := (rows 35 74 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64 255), good := (rows 167 194 133 128 144 160 192 128) }] }

theorem profile29_node116 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,129] 6 152 profile29_node116_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,129] 6 152 profile29_node116_cert).mp (by decide +kernel))

def profile29_node117_cert : Bound 8 := { allowed := (rows 152 144 16 0 0 0 0 0), upper := (rows 35 74 140 153 145 177 209 128), lower := (rows 35 74 140 8 16 32 64 128), losses := [] }

theorem profile29_node117 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,136] 6 145 profile29_node117_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,136] 6 145 profile29_node117_cert).mp (by decide +kernel))

def profile29_node118_cert : Bound 8 := { allowed := (rows 152 144 8 0 0 0 0 0), upper := (rows 35 74 148 153 153 185 217 128), lower := (rows 35 74 148 8 16 32 64 128), losses := [] }

theorem profile29_node118 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,144] 6 153 profile29_node118_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72,144] 6 153 profile29_node118_cert).mp (by decide +kernel))

def profile29_node110_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile29_node110_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node110 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,72] 6 (by decide) (choices 2) [9,17,24,129,136,144] profile29_node110_route profile29_node110_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node111
  · exact profile29_node112
  · exact profile29_node115
  · exact profile29_node116
  · exact profile29_node117
  · exact profile29_node118

def profile29_node119_cert : CutBound 8 := { lost := (rows 8 8 0 0 0 0 0 0), upper := (rows 35 131 220 216 216 248 216 128), lower := (rows 35 131 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 33 35 4 0 16 32 64 255), good := (rows 163 131 132 128 144 163 192 128) }] }

theorem profile29_node119 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,129] 6 216 profile29_node119_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,129] 6 216 profile29_node119_cert).mp (by decide +kernel))

def profile29_node120_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 35 138 221 217 217 249 217 128), lower := (rows 35 138 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 10 4 8 0 32 64 255), good := (rows 163 138 132 138 128 160 192 128) }] }

theorem profile29_node120 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,136] 6 217 profile29_node120_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,136] 6 217 profile29_node120_cert).mp (by decide +kernel))

def profile29_node121_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 35 194 157 153 153 185 217 128), lower := (rows 35 194 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 66 4 0 16 32 64 255), good := (rows 163 194 132 128 144 160 194 128) }] }

theorem profile29_node121 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,192] 6 153 profile29_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34,192] 6 153 profile29_node121_cert).mp (by decide +kernel))

def profile29_node81_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile29_node81_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node81 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [34] 6 (by decide) (choices 2) [9,24,65,72,129,136,192] profile29_node81_route profile29_node81_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node82
  · exact profile29_node91
  · exact profile29_node103
  · exact profile29_node110
  · exact profile29_node119
  · exact profile29_node120
  · exact profile29_node121

def profile29_node123_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 41 11 214 218 210 242 210 128), lower := (rows 41 11 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 6 0 18 34 66 255), good := (rows 161 247 132 128 144 160 192 128) }] }

theorem profile29_node123 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,9] 6 210 profile29_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,9] 6 210 profile29_node123_cert).mp (by decide +kernel))

def profile29_node125_cert : Bound 8 := { allowed := (rows 144 136 144 0 0 0 0 0), upper := (rows 41 19 14 216 208 240 208 128), lower := (rows 41 19 14 8 16 32 64 128), losses := [] }

theorem profile29_node125 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,10] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,10] 6 208 profile29_node125_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,10] 6 208 profile29_node125_cert).mp (by decide +kernel))

def profile29_node126_cert : Bound 8 := { allowed := (rows 144 136 136 0 0 0 0 0), upper := (rows 41 19 22 200 216 232 200 128), lower := (rows 41 19 22 8 16 32 64 128), losses := [] }

theorem profile29_node126 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,18] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,18] 6 200 profile29_node126_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,18] 6 200 profile29_node126_cert).mp (by decide +kernel))

def profile29_node127_cert : Bound 8 := { allowed := (rows 144 136 128 0 0 0 0 0), upper := (rows 41 19 28 202 210 226 194 128), lower := (rows 41 19 28 8 16 32 64 128), losses := [] }

theorem profile29_node127 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,24] 6 194 profile29_node127_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,24] 6 194 profile29_node127_cert).mp (by decide +kernel))

def profile29_node129_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 41 19 70 24 152 168 200 128), lower := (rows 41 19 70 24 16 32 64 128), losses := [{ target := 4, region := (rows 9 2 6 8 0 41 73 255), good := (rows 233 231 198 233 128 160 192 128) }] }

theorem profile29_node129 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,66,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,66,16] 6 136 profile29_node129_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,66,16] 6 136 profile29_node129_cert).mp (by decide +kernel))

def profile29_node130_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 41 19 70 136 152 184 216 128), lower := (rows 41 19 70 136 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 255 0 32 64 255), good := (rows 169 139 206 136 136 169 200 136) }] }

theorem profile29_node130 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,66,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,66,128] 6 152 profile29_node130_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,66,128] 6 152 profile29_node130_cert).mp (by decide +kernel))

def profile29_node128_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node128_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node128 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,66] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,66] 6 (by decide) (choices 1) [16,128] profile29_node128_route profile29_node128_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node129
  · exact profile29_node130


#print axioms profile29_node128
end Delivery.SmallBudgetTenFinite8
