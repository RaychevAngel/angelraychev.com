import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile20_node3_cert : CutBound 8 := { lost := (rows 64 64 0 16 0 0 0 0), upper := (rows 7 19 52 200 208 224 64 128), lower := (rows 7 19 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 239 235 236 232 232 232 232 232) },{ target := 6, region := (rows 5 6 4 8 16 32 0 255), good := (rows 135 147 183 136 144 160 128 128) }] }

theorem profile20_node3 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,48] 6 192 profile20_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,48] 6 192 profile20_node3_cert).mp (by decide +kernel))

def profile20_node4_cert : CutBound 8 := { lost := (rows 64 64 0 16 0 0 0 0), upper := (rows 7 19 84 232 240 224 64 128), lower := (rows 7 19 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 239 235 236 232 232 232 232 232) },{ target := 6, region := (rows 5 6 4 8 16 32 0 255), good := (rows 135 147 151 136 144 160 128 128) }] }

theorem profile20_node4 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,80] 6 224 profile20_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,80] 6 224 profile20_node4_cert).mp (by decide +kernel))

def profile20_node5_cert : CutBound 8 := { lost := (rows 0 0 144 0 0 0 0 0), upper := (rows 7 19 100 216 208 240 64 128), lower := (rows 7 19 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 255 255), good := (rows 199 195 228 200 192 228 192 192) },{ target := 7, region := (rows 1 2 36 8 16 32 255 0), good := (rows 71 83 100 72 80 100 64 64) }] }

theorem profile20_node5 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,96] 6 208 profile20_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,96] 6 208 profile20_node5_cert).mp (by decide +kernel))

def profile20_node6_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 7 19 196 248 240 240 64 128), lower := (rows 7 19 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 255 8 0 32 255 255), good := (rows 199 199 196 204 196 228 196 196) }] }

theorem profile20_node6 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,192] 6 240 profile20_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17,192] 6 240 profile20_node6_cert).mp (by decide +kernel))

def profile20_node2_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node2_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node2 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,17] 6 (by decide) (choices 2) [48,80,96,192] profile20_node2_route profile20_node2_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node3
  · exact profile20_node4
  · exact profile20_node5
  · exact profile20_node6

def profile20_node9_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 7 35 84 88 144 160 64 128), lower := (rows 7 35 84 88 16 32 64 128), losses := [{ target := 4, region := (rows 5 7 4 8 0 255 255 255), good := (rows 231 227 231 232 224 224 224 224) }] }

theorem profile20_node9 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,80,80] 6 128 profile20_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,80,80] 6 128 profile20_node9_cert).mp (by decide +kernel))

def profile20_node10_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 7 35 84 152 208 224 64 128), lower := (rows 7 35 84 152 16 32 64 128), losses := [{ target := 4, region := (rows 5 7 4 8 0 255 255 255), good := (rows 231 227 231 232 224 224 224 224) }] }

theorem profile20_node10 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,80,144] 6 192 profile20_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,80,144] 6 192 profile20_node10_cert).mp (by decide +kernel))

def profile20_node11_cert : CutBound 8 := { lost := (rows 64 64 0 16 0 0 0 0), upper := (rows 7 35 84 200 144 176 64 128), lower := (rows 7 35 84 200 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 32 255 255), good := (rows 207 235 204 200 200 232 200 200) },{ target := 6, region := (rows 5 7 4 8 255 255 0 255), good := (rows 183 179 183 184 176 176 176 176) }] }

theorem profile20_node11 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,80,192] 6 144 profile20_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,80,192] 6 144 profile20_node11_cert).mp (by decide +kernel))

def profile20_node8_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node8_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node8 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,80] 6 (by decide) (choices 2) [80,144,192] profile20_node8_route profile20_node8_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile20_node9
  · exact profile20_node10
  · exact profile20_node11

def profile20_node12_cert : CutBound 8 := { lost := (rows 16 16 16 0 0 0 0 0), upper := (rows 7 35 196 216 208 240 64 128), lower := (rows 7 35 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 35 34 255 8 0 32 255 255), good := (rows 199 231 196 204 196 231 196 196) }] }

theorem profile20_node12 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,192] 6 208 profile20_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33,192] 6 208 profile20_node12_cert).mp (by decide +kernel))

def profile20_node7_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node7_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node7 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,33] 6 (by decide) (choices 2) [80,192] profile20_node7_route profile20_node7_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile20_node8
  · exact profile20_node12

def profile20_node14_cert : CutBound 8 := { lost := (rows 64 0 64 16 0 0 0 0), upper := (rows 7 50 21 200 208 224 64 128), lower := (rows 7 50 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 239 234 237 232 232 232 232 232) },{ target := 6, region := (rows 3 2 6 8 16 32 0 255), good := (rows 135 183 149 136 144 160 128 128) }] }

theorem profile20_node14 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,17] 6 192 profile20_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,17] 6 192 profile20_node14_cert).mp (by decide +kernel))

def profile20_node15_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 7 50 69 216 208 240 64 128), lower := (rows 7 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 255 255), good := (rows 199 231 197 200 192 224 192 192) }] }

theorem profile20_node15 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,65] 6 208 profile20_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,65] 6 208 profile20_node15_cert).mp (by decide +kernel))

def profile20_node16_cert : CutBound 8 := { lost := (rows 128 0 128 16 0 0 0 0), upper := (rows 7 50 84 201 209 225 64 128), lower := (rows 7 50 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 239 226 196 200 192 224 192 192) },{ target := 7, region := (rows 3 2 22 8 16 32 255 0), good := (rows 71 119 84 72 84 96 64 64) }] }

theorem profile20_node16 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,80] 6 193 profile20_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,80] 6 193 profile20_node16_cert).mp (by decide +kernel))

def profile20_node17_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 7 50 196 217 209 241 64 128), lower := (rows 7 50 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 255 8 0 32 255 255), good := (rows 199 231 196 204 196 228 196 196) }] }

theorem profile20_node17 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,192] 6 209 profile20_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48,192] 6 209 profile20_node17_cert).mp (by decide +kernel))

def profile20_node13_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node13_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node13 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,48] 6 (by decide) (choices 2) [17,65,80,192] profile20_node13_route profile20_node13_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node14
  · exact profile20_node15
  · exact profile20_node16
  · exact profile20_node17

def profile20_node18_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 7 67 244 248 240 240 64 128), lower := (rows 7 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 5 7 4 8 0 32 255 255), good := (rows 199 195 199 200 192 224 192 192) }] }

theorem profile20_node18 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,65] 6 240 profile20_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,65] 6 240 profile20_node18_cert).mp (by decide +kernel))

def profile20_node20_cert : CutBound 8 := { lost := (rows 64 0 64 16 0 0 0 0), upper := (rows 7 82 21 232 240 224 64 128), lower := (rows 7 82 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 239 234 237 232 232 232 232 232) },{ target := 6, region := (rows 3 2 6 8 16 32 0 255), good := (rows 135 151 149 136 144 160 128 128) }] }

theorem profile20_node20 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,17] 6 224 profile20_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,17] 6 224 profile20_node20_cert).mp (by decide +kernel))

def profile20_node22_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 7 82 37 88 144 160 64 128), lower := (rows 7 82 37 88 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 7 8 0 255 255 255), good := (rows 231 231 229 232 224 224 224 224) }] }

theorem profile20_node22 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,33,80] 6 128 profile20_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,33,80] 6 128 profile20_node22_cert).mp (by decide +kernel))

def profile20_node23_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 7 82 37 152 208 224 64 128), lower := (rows 7 82 37 152 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 7 8 0 255 255 255), good := (rows 231 231 229 232 224 224 224 224) }] }

theorem profile20_node23 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,33,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,33,144] 6 192 profile20_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,33,144] 6 192 profile20_node23_cert).mp (by decide +kernel))

def profile20_node24_cert : CutBound 8 := { lost := (rows 64 0 64 16 0 0 0 0), upper := (rows 7 82 37 200 144 176 64 128), lower := (rows 7 82 37 200 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 32 255 255), good := (rows 207 202 237 200 200 232 200 200) },{ target := 6, region := (rows 3 2 7 8 255 255 0 255), good := (rows 183 183 181 184 176 176 176 176) }] }

theorem profile20_node24 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,33,192] 6 144 profile20_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,33,192] 6 144 profile20_node24_cert).mp (by decide +kernel))

def profile20_node21_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node21_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node21 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,33] 6 (by decide) (choices 2) [80,144,192] profile20_node21_route profile20_node21_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile20_node22
  · exact profile20_node23
  · exact profile20_node24

def profile20_node25_cert : CutBound 8 := { lost := (rows 128 128 0 16 0 0 0 0), upper := (rows 7 82 52 201 209 225 64 128), lower := (rows 7 82 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 239 194 228 200 192 224 192 192) },{ target := 7, region := (rows 5 22 4 8 16 32 255 0), good := (rows 71 82 119 72 82 96 64 64) }] }

theorem profile20_node25 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,48] 6 193 profile20_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,48] 6 193 profile20_node25_cert).mp (by decide +kernel))

def profile20_node26_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 7 82 69 184 176 176 64 128), lower := (rows 7 82 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 255 255), good := (rows 199 199 197 200 192 224 192 192) }] }

theorem profile20_node26 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,65] 6 176 profile20_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,65] 6 176 profile20_node26_cert).mp (by decide +kernel))

def profile20_node27_cert : CutBound 8 := { lost := (rows 0 0 0 80 0 0 0 0), upper := (rows 7 82 84 169 177 161 64 128), lower := (rows 7 82 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 239 194 196 200 192 224 192 192) },{ target := 6, region := (rows 1 2 4 9 17 33 0 255), good := (rows 191 146 148 136 144 160 128 128) }] }

theorem profile20_node27 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,80] 6 161 profile20_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,80] 6 161 profile20_node27_cert).mp (by decide +kernel))

def profile20_node28_cert : CutBound 8 := { lost := (rows 0 0 16 64 0 0 0 0), upper := (rows 7 82 100 153 145 177 64 128), lower := (rows 7 82 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 255 255), good := (rows 199 194 228 200 192 228 192 192) },{ target := 6, region := (rows 1 2 4 9 17 33 0 255), good := (rows 191 146 164 136 144 160 128 128) }] }

theorem profile20_node28 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,96] 6 145 profile20_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,96] 6 145 profile20_node28_cert).mp (by decide +kernel))

def profile20_node29_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 7 82 133 248 240 240 64 128), lower := (rows 7 82 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 255 255), good := (rows 199 199 197 200 192 224 192 192) }] }

theorem profile20_node29 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,129] 6 240 profile20_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,129] 6 240 profile20_node29_cert).mp (by decide +kernel))

def profile20_node30_cert : CutBound 8 := { lost := (rows 64 0 64 16 0 0 0 0), upper := (rows 7 82 148 233 241 225 64 128), lower := (rows 7 82 148 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 239 194 196 200 192 224 192 192) },{ target := 6, region := (rows 3 2 22 8 16 32 0 255), good := (rows 135 151 148 136 148 160 128 128) }] }

theorem profile20_node30 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,144] 6 225 profile20_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,144] 6 225 profile20_node30_cert).mp (by decide +kernel))

def profile20_node31_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 7 82 164 217 209 241 64 128), lower := (rows 7 82 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 255 255), good := (rows 199 194 228 200 192 228 192 192) },{ target := 6, region := (rows 1 2 36 8 16 32 0 255), good := (rows 135 146 164 136 144 164 128 128) }] }

theorem profile20_node31 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,160] 6 209 profile20_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,160] 6 209 profile20_node31_cert).mp (by decide +kernel))

def profile20_node32_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 7 82 196 185 177 177 64 128), lower := (rows 7 82 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 255 8 0 32 255 255), good := (rows 199 199 196 204 196 228 196 196) }] }

theorem profile20_node32 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,192] 6 177 profile20_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80,192] 6 177 profile20_node32_cert).mp (by decide +kernel))

def profile20_node19_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node19_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node19 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,80] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile20_node19_route profile20_node19_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node20
  · exact profile20_node21
  · exact profile20_node25
  · exact profile20_node26
  · exact profile20_node27
  · exact profile20_node28
  · exact profile20_node29
  · exact profile20_node30
  · exact profile20_node31
  · exact profile20_node32

def profile20_node33_cert : CutBound 8 := { lost := (rows 0 144 0 0 0 0 0 0), upper := (rows 7 98 213 217 209 241 64 128), lower := (rows 7 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 199 226 196 200 192 226 192 192) },{ target := 7, region := (rows 1 34 4 8 16 32 255 0), good := (rows 71 98 68 72 80 98 64 64) }] }

theorem profile20_node33 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,96] 6 209 profile20_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,96] 6 209 profile20_node33_cert).mp (by decide +kernel))

def profile20_node34_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 7 194 245 249 241 241 64 128), lower := (rows 7 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 5 255 4 8 0 32 255 255), good := (rows 199 194 199 202 194 226 194 194) }] }

theorem profile20_node34 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,192] 6 241 profile20_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6,192] 6 241 profile20_node34_cert).mp (by decide +kernel))

def profile20_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node1 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [6] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile20_node1_route profile20_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node2
  · exact profile20_node7
  · exact profile20_node13
  · exact profile20_node18
  · exact profile20_node19
  · exact profile20_node33
  · exact profile20_node34

def profile20_node37_cert : CutBound 8 := { lost := (rows 64 64 0 16 0 0 0 0), upper := (rows 19 7 52 200 208 224 64 128), lower := (rows 19 7 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 235 239 236 232 232 232 232 232) },{ target := 6, region := (rows 5 6 4 8 16 32 0 255), good := (rows 147 135 183 136 144 160 128 128) }] }

theorem profile20_node37 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,48] 6 192 profile20_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,48] 6 192 profile20_node37_cert).mp (by decide +kernel))

def profile20_node38_cert : CutBound 8 := { lost := (rows 64 64 0 16 0 0 0 0), upper := (rows 19 7 84 232 240 224 64 128), lower := (rows 19 7 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 235 239 236 232 232 232 232 232) },{ target := 6, region := (rows 5 6 4 8 16 32 0 255), good := (rows 147 135 151 136 144 160 128 128) }] }

theorem profile20_node38 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,80] 6 224 profile20_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,80] 6 224 profile20_node38_cert).mp (by decide +kernel))

def profile20_node39_cert : CutBound 8 := { lost := (rows 0 0 144 0 0 0 0 0), upper := (rows 19 7 100 216 208 240 64 128), lower := (rows 19 7 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 255 255), good := (rows 195 199 228 200 192 228 192 192) },{ target := 7, region := (rows 1 2 36 8 16 32 255 0), good := (rows 83 71 100 72 80 100 64 64) }] }

theorem profile20_node39 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,96] 6 208 profile20_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,96] 6 208 profile20_node39_cert).mp (by decide +kernel))

def profile20_node40_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 19 7 196 248 240 240 64 128), lower := (rows 19 7 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 255 8 0 32 255 255), good := (rows 199 199 196 204 196 228 196 196) }] }

theorem profile20_node40 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,192] 6 240 profile20_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5,192] 6 240 profile20_node40_cert).mp (by decide +kernel))

def profile20_node36_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node36_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node36 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,5] 6 (by decide) (choices 2) [48,80,96,192] profile20_node36_route profile20_node36_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node37
  · exact profile20_node38
  · exact profile20_node39
  · exact profile20_node40

def profile20_node41_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 19 19 228 236 244 228 64 128), lower := (rows 19 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 239 239 236 236 236 236 236 236) }] }

theorem profile20_node41 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,17] 6 228 profile20_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,17] 6 228 profile20_node41_cert).mp (by decide +kernel))

def profile20_node42_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 19 22 229 233 241 225 64 128), lower := (rows 19 22 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 239 198 196 200 192 224 192 192) }] }

theorem profile20_node42 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,20] 6 225 profile20_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,20] 6 225 profile20_node42_cert).mp (by decide +kernel))

def profile20_node44_cert : CutBound 8 := { lost := (rows 0 0 128 16 0 0 0 0), upper := (rows 19 35 84 204 212 228 64 128), lower := (rows 19 35 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 255 255), good := (rows 195 227 236 200 192 224 192 192) },{ target := 7, region := (rows 1 2 21 8 16 32 255 0), good := (rows 87 103 84 72 84 96 64 64) }] }

theorem profile20_node44 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,80] 6 196 profile20_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,80] 6 196 profile20_node44_cert).mp (by decide +kernel))

def profile20_node46_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 19 35 196 28 208 224 64 128), lower := (rows 19 35 196 28 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 255 8 0 255 255 255), good := (rows 231 231 228 236 228 228 228 228) }] }

theorem profile20_node46 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,20] 6 192 profile20_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,20] 6 192 profile20_node46_cert).mp (by decide +kernel))

def profile20_node47_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 19 35 196 76 144 176 64 128), lower := (rows 19 35 196 76 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 32 255 255), good := (rows 207 239 204 204 204 236 204 204) }] }

theorem profile20_node47 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,68] 6 144 profile20_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,68] 6 144 profile20_node47_cert).mp (by decide +kernel))

def profile20_node48_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 19 35 196 88 148 164 64 128), lower := (rows 19 35 196 88 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 255 8 0 255 255 255), good := (rows 231 231 228 236 228 228 228 228) }] }

theorem profile20_node48 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,80] 6 132 profile20_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,80] 6 132 profile20_node48_cert).mp (by decide +kernel))

def profile20_node49_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 19 35 196 200 20 52 64 128), lower := (rows 19 35 196 200 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 32 255 255), good := (rows 207 239 204 204 204 236 204 204) }] }

theorem profile20_node49 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,192] 6 20 profile20_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192,192] 6 20 profile20_node49_cert).mp (by decide +kernel))

def profile20_node45_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node45_route : Route 8 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node45 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33,192] 6 (by decide) (choices 2) [20,68,80,192] profile20_node45_route profile20_node45_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node46
  · exact profile20_node47
  · exact profile20_node48
  · exact profile20_node49

def profile20_node43_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node43_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node43 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,33] 6 (by decide) (choices 2) [80,192] profile20_node43_route profile20_node43_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile20_node44
  · exact profile20_node45

def profile20_node51_cert : CutBound 8 := { lost := (rows 0 16 0 16 0 0 0 0), upper := (rows 19 38 21 200 208 224 64 128), lower := (rows 19 38 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 6 4 255 0 255 255 255), good := (rows 235 238 239 232 232 232 232 232) }] }

theorem profile20_node51 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,17] 6 192 profile20_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,17] 6 192 profile20_node51_cert).mp (by decide +kernel))

def profile20_node52_cert : CutBound 8 := { lost := (rows 0 0 144 0 0 0 0 0), upper := (rows 19 38 69 216 208 240 64 128), lower := (rows 19 38 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 199 230 197 200 192 224 192 192) },{ target := 7, region := (rows 1 2 5 8 16 32 255 0), good := (rows 87 102 69 72 80 96 64 64) }] }

theorem profile20_node52 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,65] 6 208 profile20_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,65] 6 208 profile20_node52_cert).mp (by decide +kernel))

def profile20_node53_cert : CutBound 8 := { lost := (rows 0 0 128 16 0 0 0 0), upper := (rows 19 38 84 201 209 225 64 128), lower := (rows 19 38 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 235 230 196 200 192 224 192 192) },{ target := 7, region := (rows 1 2 21 8 16 32 255 0), good := (rows 87 102 84 72 84 96 64 64) }] }

theorem profile20_node53 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,80] 6 193 profile20_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,80] 6 193 profile20_node53_cert).mp (by decide +kernel))

def profile20_node54_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 19 38 196 217 209 241 64 128), lower := (rows 19 38 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 255 8 0 32 255 255), good := (rows 199 230 196 204 196 230 196 196) }] }

theorem profile20_node54 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,192] 6 209 profile20_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36,192] 6 209 profile20_node54_cert).mp (by decide +kernel))

def profile20_node50_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node50_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node50 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,36] 6 (by decide) (choices 2) [17,65,80,192] profile20_node50_route profile20_node50_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node51
  · exact profile20_node52
  · exact profile20_node53
  · exact profile20_node54

def profile20_node55_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 19 50 197 205 213 229 64 128), lower := (rows 19 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 239 226 196 200 192 224 192 192) }] }

theorem profile20_node55 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,48] 6 197 profile20_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,48] 6 197 profile20_node55_cert).mp (by decide +kernel))

def profile20_node56_cert : CutBound 8 := { lost := (rows 128 144 0 0 0 0 0 0), upper := (rows 19 67 244 252 244 244 64 128), lower := (rows 19 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 7, region := (rows 17 19 4 8 16 32 255 0), good := (rows 83 67 68 72 83 96 64 64) }] }

theorem profile20_node56 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,65] 6 244 profile20_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,65] 6 244 profile20_node56_cert).mp (by decide +kernel))

def profile20_node57_cert : CutBound 8 := { lost := (rows 0 144 0 0 0 0 0 0), upper := (rows 19 70 245 249 241 241 64 128), lower := (rows 19 70 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 255 255), good := (rows 195 198 198 200 192 224 192 192) },{ target := 7, region := (rows 1 6 4 8 16 32 255 0), good := (rows 83 70 70 72 80 96 64 64) }] }

theorem profile20_node57 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,68] 6 241 profile20_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,68] 6 241 profile20_node57_cert).mp (by decide +kernel))

def profile20_node58_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 19 82 229 237 245 229 64 128), lower := (rows 19 82 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 239 194 196 200 192 224 192 192) }] }

theorem profile20_node58 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,80] 6 229 profile20_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,80] 6 229 profile20_node58_cert).mp (by decide +kernel))

def profile20_node59_cert : CutBound 8 := { lost := (rows 0 144 0 0 0 0 0 0), upper := (rows 19 98 213 221 213 245 64 128), lower := (rows 19 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 195 226 196 200 192 226 192 192) },{ target := 7, region := (rows 1 34 4 8 16 32 255 0), good := (rows 83 98 68 72 80 98 64 64) }] }

theorem profile20_node59 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,96] 6 213 profile20_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,96] 6 213 profile20_node59_cert).mp (by decide +kernel))

def profile20_node61_cert : CutBound 8 := { lost := (rows 0 16 0 16 0 0 0 0), upper := (rows 19 194 21 236 244 228 64 128), lower := (rows 19 194 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 12 0 36 255 255), good := (rows 195 194 239 202 194 226 194 194) }] }

theorem profile20_node61 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,17] 6 228 profile20_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,17] 6 228 profile20_node61_cert).mp (by decide +kernel))

def profile20_node63_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 19 194 37 28 208 224 64 128), lower := (rows 19 194 37 28 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 255 255 255), good := (rows 231 226 231 238 226 226 226 226) }] }

theorem profile20_node63 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,20] 6 192 profile20_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,20] 6 192 profile20_node63_cert).mp (by decide +kernel))

def profile20_node64_cert : CutBound 8 := { lost := (rows 0 16 0 16 0 0 0 0), upper := (rows 19 194 37 76 144 176 64 128), lower := (rows 19 194 37 76 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 12 0 32 255 255), good := (rows 195 194 239 206 194 226 194 194) }] }

theorem profile20_node64 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,68] 6 144 profile20_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,68] 6 144 profile20_node64_cert).mp (by decide +kernel))

def profile20_node65_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 19 194 37 88 148 164 64 128), lower := (rows 19 194 37 88 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 37 255 255), good := (rows 231 194 231 202 194 226 194 194) }] }

theorem profile20_node65 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,80] 6 132 profile20_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,80] 6 132 profile20_node65_cert).mp (by decide +kernel))

def profile20_node66_cert : CutBound 8 := { lost := (rows 0 16 0 16 0 0 0 0), upper := (rows 19 194 37 200 20 52 64 128), lower := (rows 19 194 37 200 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 32 255 255), good := (rows 203 202 239 202 202 234 202 202) }] }

theorem profile20_node66 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,192] 6 20 profile20_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33,192] 6 20 profile20_node66_cert).mp (by decide +kernel))

def profile20_node62_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node62_route : Route 8 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node62 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,33] 6 (by decide) (choices 2) [20,68,80,192] profile20_node62_route profile20_node62_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node63
  · exact profile20_node64
  · exact profile20_node65
  · exact profile20_node66

def profile20_node69_cert : CutBound 8 := { lost := (rows 0 16 64 64 0 0 0 0), upper := (rows 19 194 52 13 80 160 64 128), lower := (rows 19 194 52 13 80 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 255 255 255), good := (rows 227 226 230 239 226 226 226 226) },{ target := 6, region := (rows 1 2 21 9 16 255 0 255), good := (rows 191 162 180 173 180 160 160 160) }] }

theorem profile20_node69 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,5,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,5,64] 6 128 profile20_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,5,64] 6 128 profile20_node69_cert).mp (by decide +kernel))

def profile20_node68_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile20_node68_route : Route 8 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node68 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,5] 6 (by decide) (choices 1) [64] profile20_node68_route profile20_node68_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node69

def profile20_node70_cert : CutBound 8 := { lost := (rows 0 16 0 16 0 0 0 0), upper := (rows 19 194 52 73 148 164 64 128), lower := (rows 19 194 52 73 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 9 0 36 255 255), good := (rows 203 194 230 203 194 226 194 194) }] }

theorem profile20_node70 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,65] 6 132 profile20_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,65] 6 132 profile20_node70_cert).mp (by decide +kernel))

def profile20_node71_cert : CutBound 8 := { lost := (rows 0 16 0 16 0 0 0 0), upper := (rows 19 194 52 76 145 161 64 128), lower := (rows 19 194 52 76 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 12 0 33 255 255), good := (rows 227 194 238 206 194 226 194 194) }] }

theorem profile20_node71 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,68] 6 129 profile20_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,68] 6 129 profile20_node71_cert).mp (by decide +kernel))

def profile20_node72_cert : Bound 8 := { allowed := (rows 192 16 192 16 0 0 0 0), upper := (rows 19 194 52 200 21 37 64 128), lower := (rows 19 194 52 200 16 32 64 128), losses := [] }

theorem profile20_node72 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,192] 6 5 profile20_node72_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48,192] 6 5 profile20_node72_cert).mp (by decide +kernel))

def profile20_node67_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node67_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node67 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,48] 6 (by decide) (choices 2) [5,65,68,192] profile20_node67_route profile20_node67_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node68
  · exact profile20_node70
  · exact profile20_node71
  · exact profile20_node72

def profile20_node73_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 19 194 69 188 180 180 64 128), lower := (rows 19 194 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 199 194 199 202 194 226 194 194) }] }

theorem profile20_node73 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,65] 6 180 profile20_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,65] 6 180 profile20_node73_cert).mp (by decide +kernel))

def profile20_node74_cert : Bound 8 := { allowed := (rows 192 0 128 208 0 0 0 0), upper := (rows 19 194 84 173 181 165 64 128), lower := (rows 19 194 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 195 194 198 202 194 226 194 194) }] }

theorem profile20_node74 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,80] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,80] 6 165 profile20_node74_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,80] 6 165 profile20_node74_cert).mp (by decide +kernel))

def profile20_node75_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 19 194 100 157 149 181 64 128), lower := (rows 19 194 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 36 8 0 32 255 255), good := (rows 195 194 230 202 194 230 194 194) }] }

theorem profile20_node75 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,96] 6 149 profile20_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,96] 6 149 profile20_node75_cert).mp (by decide +kernel))

def profile20_node76_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 19 194 196 61 53 53 64 128), lower := (rows 19 194 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 255 8 0 32 255 255), good := (rows 199 198 198 206 198 230 198 198) }] }

theorem profile20_node76 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,192] 6 53 profile20_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192,192] 6 53 profile20_node76_cert).mp (by decide +kernel))

def profile20_node60_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node60_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node60 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18,192] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile20_node60_route profile20_node60_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node61
  · exact profile20_node62
  · exact profile20_node67
  · exact profile20_node73
  · exact profile20_node74
  · exact profile20_node75
  · exact profile20_node76

def profile20_node35_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node35_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node35 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [18] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] profile20_node35_route profile20_node35_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node36
  · exact profile20_node41
  · exact profile20_node42
  · exact profile20_node43
  · exact profile20_node50
  · exact profile20_node55
  · exact profile20_node56
  · exact profile20_node57
  · exact profile20_node58
  · exact profile20_node59
  · exact profile20_node60

def profile20_node80_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 35 7 84 88 144 160 64 128), lower := (rows 35 7 84 88 16 32 64 128), losses := [{ target := 4, region := (rows 7 6 4 8 0 255 255 255), good := (rows 227 231 231 232 224 224 224 224) }] }

theorem profile20_node80 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,80,80] 6 128 profile20_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,80,80] 6 128 profile20_node80_cert).mp (by decide +kernel))

def profile20_node81_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 35 7 84 152 208 224 64 128), lower := (rows 35 7 84 152 16 32 64 128), losses := [{ target := 4, region := (rows 7 6 4 8 0 255 255 255), good := (rows 227 231 231 232 224 224 224 224) }] }

theorem profile20_node81 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,80,144] 6 192 profile20_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,80,144] 6 192 profile20_node81_cert).mp (by decide +kernel))

def profile20_node82_cert : CutBound 8 := { lost := (rows 64 64 0 16 0 0 0 0), upper := (rows 35 7 84 200 144 176 64 128), lower := (rows 35 7 84 200 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 32 255 255), good := (rows 235 207 204 200 200 232 200 200) },{ target := 6, region := (rows 7 6 4 8 255 255 0 255), good := (rows 179 183 183 184 176 176 176 176) }] }

theorem profile20_node82 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,80,192] 6 144 profile20_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,80,192] 6 144 profile20_node82_cert).mp (by decide +kernel))

def profile20_node79_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node79_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node79 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,80] 6 (by decide) (choices 2) [80,144,192] profile20_node79_route profile20_node79_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile20_node80
  · exact profile20_node81
  · exact profile20_node82

def profile20_node83_cert : CutBound 8 := { lost := (rows 16 16 16 0 0 0 0 0), upper := (rows 35 7 196 216 208 240 64 128), lower := (rows 35 7 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 35 255 8 0 32 255 255), good := (rows 231 199 196 204 196 231 196 196) }] }

theorem profile20_node83 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,192] 6 208 profile20_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5,192] 6 208 profile20_node83_cert).mp (by decide +kernel))

def profile20_node78_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node78_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node78 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,5] 6 (by decide) (choices 2) [80,192] profile20_node78_route profile20_node78_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile20_node79
  · exact profile20_node83

def profile20_node85_cert : CutBound 8 := { lost := (rows 0 0 128 16 0 0 0 0), upper := (rows 35 19 84 204 212 228 64 128), lower := (rows 35 19 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 255 255), good := (rows 227 195 236 200 192 224 192 192) },{ target := 7, region := (rows 1 2 22 8 16 32 255 0), good := (rows 103 87 84 72 84 96 64 64) }] }

theorem profile20_node85 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,80] 6 196 profile20_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,80] 6 196 profile20_node85_cert).mp (by decide +kernel))

def profile20_node87_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 35 19 196 28 208 224 64 128), lower := (rows 35 19 196 28 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 255 8 0 255 255 255), good := (rows 231 231 228 236 228 228 228 228) }] }

theorem profile20_node87 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,20] 6 192 profile20_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,20] 6 192 profile20_node87_cert).mp (by decide +kernel))

def profile20_node88_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 35 19 196 76 144 176 64 128), lower := (rows 35 19 196 76 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 32 255 255), good := (rows 239 207 204 204 204 236 204 204) }] }

theorem profile20_node88 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,68] 6 144 profile20_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,68] 6 144 profile20_node88_cert).mp (by decide +kernel))

def profile20_node89_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 35 19 196 88 148 164 64 128), lower := (rows 35 19 196 88 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 255 8 0 255 255 255), good := (rows 231 231 228 236 228 228 228 228) }] }

theorem profile20_node89 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,80] 6 132 profile20_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,80] 6 132 profile20_node89_cert).mp (by decide +kernel))

def profile20_node90_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 35 19 196 200 20 52 64 128), lower := (rows 35 19 196 200 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 32 255 255), good := (rows 239 207 204 204 204 236 204 204) }] }

theorem profile20_node90 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,192] 6 20 profile20_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192,192] 6 20 profile20_node90_cert).mp (by decide +kernel))

def profile20_node86_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node86_route : Route 8 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node86 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17,192] 6 (by decide) (choices 2) [20,68,80,192] profile20_node86_route profile20_node86_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node87
  · exact profile20_node88
  · exact profile20_node89
  · exact profile20_node90

def profile20_node84_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node84_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node84 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,17] 6 (by decide) (choices 2) [80,192] profile20_node84_route profile20_node84_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile20_node85
  · exact profile20_node86

def profile20_node92_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 35 22 21 200 208 224 64 128), lower := (rows 35 22 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 255 0 255 255 255), good := (rows 235 239 237 232 232 232 232 232) }] }

theorem profile20_node92 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,17] 6 192 profile20_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,17] 6 192 profile20_node92_cert).mp (by decide +kernel))

def profile20_node93_cert : CutBound 8 := { lost := (rows 0 0 144 0 0 0 0 0), upper := (rows 35 22 69 216 208 240 64 128), lower := (rows 35 22 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 231 198 197 200 192 224 192 192) },{ target := 7, region := (rows 1 2 5 8 16 32 255 0), good := (rows 103 86 69 72 80 96 64 64) }] }

theorem profile20_node93 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,65] 6 208 profile20_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,65] 6 208 profile20_node93_cert).mp (by decide +kernel))

def profile20_node94_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 35 22 84 201 209 225 64 128), lower := (rows 35 22 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 11 0 35 255 255), good := (rows 235 239 196 200 192 224 192 192) }] }

theorem profile20_node94 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,80] 6 193 profile20_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,80] 6 193 profile20_node94_cert).mp (by decide +kernel))

def profile20_node96_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 35 22 196 25 208 224 64 128), lower := (rows 35 22 196 25 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 255 8 0 255 255 255), good := (rows 231 231 228 237 228 228 228 228) }] }

theorem profile20_node96 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,17] 6 192 profile20_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,17] 6 192 profile20_node96_cert).mp (by decide +kernel))

def profile20_node97_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 35 22 196 73 144 176 64 128), lower := (rows 35 22 196 73 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 9 0 32 255 255), good := (rows 239 198 196 205 196 228 196 196) }] }

theorem profile20_node97 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,65] 6 144 profile20_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,65] 6 144 profile20_node97_cert).mp (by decide +kernel))

def profile20_node98_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 35 22 196 88 145 161 64 128), lower := (rows 35 22 196 88 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 255 8 0 35 255 255), good := (rows 231 231 196 204 196 228 196 196) }] }

theorem profile20_node98 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,80] 6 129 profile20_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,80] 6 129 profile20_node98_cert).mp (by decide +kernel))

def profile20_node99_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 35 22 196 200 17 49 64 128), lower := (rows 35 22 196 200 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 32 255 255), good := (rows 239 206 204 204 204 236 204 204) }] }

theorem profile20_node99 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,192] 6 17 profile20_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192,192] 6 17 profile20_node99_cert).mp (by decide +kernel))

def profile20_node95_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node95_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node95 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20,192] 6 (by decide) (choices 2) [17,65,80,192] profile20_node95_route profile20_node95_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node96
  · exact profile20_node97
  · exact profile20_node98
  · exact profile20_node99

def profile20_node91_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node91_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node91 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,20] 6 (by decide) (choices 2) [17,65,80,192] profile20_node91_route profile20_node91_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node92
  · exact profile20_node93
  · exact profile20_node94
  · exact profile20_node95

def profile20_node100_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 35 67 212 220 212 244 64 128), lower := (rows 35 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 255 255), good := (rows 227 195 196 200 192 227 192 192) }] }

theorem profile20_node100 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,65] 6 212 profile20_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,65] 6 212 profile20_node100_cert).mp (by decide +kernel))

def profile20_node101_cert : CutBound 8 := { lost := (rows 0 144 0 0 0 0 0 0), upper := (rows 35 70 213 217 209 241 64 128), lower := (rows 35 70 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 255 255), good := (rows 227 198 198 200 192 224 192 192) },{ target := 7, region := (rows 1 6 4 8 16 32 255 0), good := (rows 99 70 70 72 80 96 64 64) }] }

theorem profile20_node101 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,68] 6 209 profile20_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,68] 6 209 profile20_node101_cert).mp (by decide +kernel))

def profile20_node103_cert : CutBound 8 := { lost := (rows 0 128 0 16 0 0 0 0), upper := (rows 35 82 21 204 212 228 64 128), lower := (rows 35 82 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 255 255), good := (rows 227 194 237 200 192 224 192 192) },{ target := 7, region := (rows 1 22 4 8 16 32 255 0), good := (rows 99 82 87 72 82 96 64 64) }] }

theorem profile20_node103 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,17] 6 196 profile20_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,17] 6 196 profile20_node103_cert).mp (by decide +kernel))

def profile20_node104_cert : CutBound 8 := { lost := (rows 0 0 16 64 0 0 0 0), upper := (rows 35 82 69 156 148 180 64 128), lower := (rows 35 82 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 231 194 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 4 12 20 36 0 255), good := (rows 163 146 189 136 144 160 128 128) }] }

theorem profile20_node104 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,65] 6 148 profile20_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,65] 6 148 profile20_node104_cert).mp (by decide +kernel))

def profile20_node105_cert : CutBound 8 := { lost := (rows 0 128 128 0 0 0 0 0), upper := (rows 35 82 84 141 149 165 64 128), lower := (rows 35 82 84 8 16 32 64 128), losses := [{ target := 7, region := (rows 1 22 22 8 16 32 255 0), good := (rows 103 86 86 72 86 96 64 64) }] }

theorem profile20_node105 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,80] 6 133 profile20_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,80] 6 133 profile20_node105_cert).mp (by decide +kernel))

def profile20_node106_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 35 82 133 220 212 244 64 128), lower := (rows 35 82 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 231 194 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 167 146 133 136 144 160 128 128) }] }

theorem profile20_node106 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,129] 6 212 profile20_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,129] 6 212 profile20_node106_cert).mp (by decide +kernel))

def profile20_node107_cert : CutBound 8 := { lost := (rows 0 128 64 0 0 0 0 0), upper := (rows 35 82 148 205 213 229 64 128), lower := (rows 35 82 148 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 2 22 8 16 32 0 255), good := (rows 167 150 148 136 148 160 128 128) },{ target := 7, region := (rows 1 22 4 8 16 32 255 0), good := (rows 99 82 86 72 82 96 64 64) }] }

theorem profile20_node107 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,144] 6 197 profile20_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,144] 6 197 profile20_node107_cert).mp (by decide +kernel))

def profile20_node108_cert : CutBound 8 := { lost := (rows 0 128 16 0 0 0 0 0), upper := (rows 35 82 196 157 149 181 64 128), lower := (rows 35 82 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 231 198 196 204 196 228 196 196) },{ target := 7, region := (rows 1 18 4 8 16 32 255 0), good := (rows 99 82 68 72 82 96 64 64) }] }

theorem profile20_node108 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,192] 6 149 profile20_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80,192] 6 149 profile20_node108_cert).mp (by decide +kernel))

def profile20_node102_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node102_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node102 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,80] 6 (by decide) (choices 2) [17,65,80,129,144,192] profile20_node102_route profile20_node102_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node103
  · exact profile20_node104
  · exact profile20_node105
  · exact profile20_node106
  · exact profile20_node107
  · exact profile20_node108

def profile20_node109_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 35 194 213 221 213 245 64 128), lower := (rows 35 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 255 4 8 0 32 255 255), good := (rows 227 194 198 202 194 227 194 194) }] }

theorem profile20_node109 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,192] 6 213 profile20_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34,192] 6 213 profile20_node109_cert).mp (by decide +kernel))

def profile20_node77_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 12 => 3 | 36 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node77_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node77 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [34] 6 (by decide) (choices 2) [5,17,20,65,68,80,192] profile20_node77_route profile20_node77_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node78
  · exact profile20_node84
  · exact profile20_node91
  · exact profile20_node100
  · exact profile20_node101
  · exact profile20_node102
  · exact profile20_node109

def profile20_node112_cert : CutBound 8 := { lost := (rows 0 64 64 16 0 0 0 0), upper := (rows 49 7 22 200 208 224 64 128), lower := (rows 49 7 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 233 239 238 232 232 232 232 232) },{ target := 6, region := (rows 1 3 5 8 16 32 0 255), good := (rows 183 135 150 136 144 160 128 128) }] }

theorem profile20_node112 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,18] 6 192 profile20_node112_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,18] 6 192 profile20_node112_cert).mp (by decide +kernel))

def profile20_node113_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 49 7 70 216 208 240 64 128), lower := (rows 49 7 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 7 8 0 32 255 255), good := (rows 231 199 198 200 192 224 192 192) }] }

theorem profile20_node113 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,66] 6 208 profile20_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,66] 6 208 profile20_node113_cert).mp (by decide +kernel))

def profile20_node114_cert : CutBound 8 := { lost := (rows 0 128 128 16 0 0 0 0), upper := (rows 49 7 84 202 210 226 64 128), lower := (rows 49 7 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 255 255), good := (rows 225 239 196 200 192 224 192 192) },{ target := 7, region := (rows 1 3 21 8 16 32 255 0), good := (rows 119 71 84 72 84 96 64 64) }] }

theorem profile20_node114 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,80] 6 194 profile20_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,80] 6 194 profile20_node114_cert).mp (by decide +kernel))

def profile20_node115_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 49 7 196 218 210 242 64 128), lower := (rows 49 7 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 255 8 0 32 255 255), good := (rows 231 199 196 204 196 228 196 196) }] }

theorem profile20_node115 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,192] 6 210 profile20_node115_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5,192] 6 210 profile20_node115_cert).mp (by decide +kernel))

def profile20_node111_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node111_route : Route 8 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node111 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,5] 6 (by decide) (choices 2) [18,66,80,192] profile20_node111_route profile20_node111_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node112
  · exact profile20_node113
  · exact profile20_node114
  · exact profile20_node115

def profile20_node116_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 49 19 198 206 214 230 64 128), lower := (rows 49 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 255 255), good := (rows 225 239 196 200 192 224 192 192) }] }

theorem profile20_node116 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,17] 6 198 profile20_node116_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,17] 6 198 profile20_node116_cert).mp (by decide +kernel))

def profile20_node118_cert : CutBound 8 := { lost := (rows 0 64 64 16 0 0 0 0), upper := (rows 49 22 7 200 208 224 64 128), lower := (rows 49 22 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 233 238 239 232 232 232 232 232) },{ target := 6, region := (rows 1 3 5 8 16 32 0 255), good := (rows 183 150 135 136 144 160 128 128) }] }

theorem profile20_node118 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,3] 6 192 profile20_node118_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,3] 6 192 profile20_node118_cert).mp (by decide +kernel))

def profile20_node119_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 49 22 69 202 210 226 64 128), lower := (rows 49 22 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 255 255), good := (rows 229 238 197 200 192 224 192 192) }] }

theorem profile20_node119 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,65] 6 194 profile20_node119_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,65] 6 194 profile20_node119_cert).mp (by decide +kernel))

def profile20_node120_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 49 22 70 201 209 225 64 128), lower := (rows 49 22 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 198 198 200 192 224 192 192) }] }

theorem profile20_node120 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,66] 6 193 profile20_node120_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,66] 6 193 profile20_node120_cert).mp (by decide +kernel))

def profile20_node123_cert : CutBound 8 := { lost := (rows 64 0 16 64 0 0 0 0), upper := (rows 49 22 196 11 80 160 64 128), lower := (rows 49 22 196 11 80 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 255 255 255), good := (rows 229 230 228 239 228 228 228 228) },{ target := 6, region := (rows 19 2 4 10 16 255 0 255), good := (rows 177 191 164 171 177 160 160 160) }] }

theorem profile20_node123 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,3,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,3,64] 6 128 profile20_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,3,64] 6 128 profile20_node123_cert).mp (by decide +kernel))

def profile20_node122_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile20_node122_route : Route 8 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node122 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,3] 6 (by decide) (choices 1) [64] profile20_node122_route profile20_node122_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node123

def profile20_node124_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 49 22 196 73 146 162 64 128), lower := (rows 49 22 196 73 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 9 0 34 255 255), good := (rows 237 230 196 205 196 228 196 196) }] }

theorem profile20_node124 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,65] 6 130 profile20_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,65] 6 130 profile20_node124_cert).mp (by decide +kernel))

def profile20_node125_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 49 22 196 74 145 161 64 128), lower := (rows 49 22 196 74 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 10 0 33 255 255), good := (rows 229 206 196 206 196 228 196 196) }] }

theorem profile20_node125 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,66] 6 129 profile20_node125_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,66] 6 129 profile20_node125_cert).mp (by decide +kernel))

def profile20_node126_cert : Bound 8 := { allowed := (rows 192 192 16 16 0 0 0 0), upper := (rows 49 22 196 200 19 35 64 128), lower := (rows 49 22 196 200 16 32 64 128), losses := [] }

theorem profile20_node126 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,192] 6 3 profile20_node126_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192,192] 6 3 profile20_node126_cert).mp (by decide +kernel))

def profile20_node121_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node121_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node121 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20,192] 6 (by decide) (choices 2) [3,65,66,192] profile20_node121_route profile20_node121_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node122
  · exact profile20_node124
  · exact profile20_node125
  · exact profile20_node126

def profile20_node117_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node117_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node117 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,20] 6 (by decide) (choices 2) [3,65,66,192] profile20_node117_route profile20_node117_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node118
  · exact profile20_node119
  · exact profile20_node120
  · exact profile20_node121

def profile20_node127_cert : CutBound 8 := { lost := (rows 0 144 0 0 0 0 0 0), upper := (rows 49 67 214 222 214 246 64 128), lower := (rows 49 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 227 195 196 200 192 224 192 192) },{ target := 7, region := (rows 1 3 4 8 16 32 255 0), good := (rows 115 67 68 72 80 96 64 64) }] }

theorem profile20_node127 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,65] 6 214 profile20_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,65] 6 214 profile20_node127_cert).mp (by decide +kernel))

def profile20_node128_cert : CutBound 8 := { lost := (rows 0 144 0 0 0 0 0 0), upper := (rows 49 70 215 219 211 243 64 128), lower := (rows 49 70 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 255 255), good := (rows 225 198 198 200 192 224 192 192) },{ target := 7, region := (rows 1 6 4 8 16 32 255 0), good := (rows 113 70 70 72 80 96 64 64) }] }

theorem profile20_node128 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,68] 6 211 profile20_node128_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,68] 6 211 profile20_node128_cert).mp (by decide +kernel))

def profile20_node130_cert : CutBound 8 := { lost := (rows 0 128 128 16 0 0 0 0), upper := (rows 49 82 7 204 212 228 64 128), lower := (rows 49 82 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 255 255), good := (rows 225 194 239 200 192 224 192 192) },{ target := 7, region := (rows 1 19 5 8 16 32 255 0), good := (rows 119 82 71 72 82 96 64 64) }] }

theorem profile20_node130 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,3] 6 196 profile20_node130_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,3] 6 196 profile20_node130_cert).mp (by decide +kernel))


#print axioms profile20_node130
end Delivery.SmallBudgetTenFinite8
