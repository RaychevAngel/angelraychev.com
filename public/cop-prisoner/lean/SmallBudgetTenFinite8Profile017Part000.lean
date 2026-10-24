import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile17_node2_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 57 11 212 216 208 240 64 128), lower := (rows 57 11 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 247 244 244 244 244 244 244) }] }

theorem profile17_node2 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,9] 6 208 profile17_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,9] 6 208 profile17_node2_cert).mp (by decide +kernel))

def profile17_node3_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 57 26 197 201 209 225 64 128), lower := (rows 57 26 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 255 255), good := (rows 245 210 196 192 208 224 192 192) }] }

theorem profile17_node3 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,24] 6 193 profile17_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,24] 6 193 profile17_node3_cert).mp (by decide +kernel))

def profile17_node4_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 57 67 220 216 216 248 64 128), lower := (rows 57 67 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 255 255), good := (rows 243 195 196 192 208 224 192 192) }] }

theorem profile17_node4 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,65] 6 216 profile17_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,65] 6 216 profile17_node4_cert).mp (by decide +kernel))

def profile17_node5_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 57 74 213 217 209 241 64 128), lower := (rows 57 74 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 255 255), good := (rows 245 194 196 192 208 224 192 192) }] }

theorem profile17_node5 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,72] 6 209 profile17_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,72] 6 209 profile17_node5_cert).mp (by decide +kernel))

def profile17_node6_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 57 194 221 217 217 249 64 128), lower := (rows 57 194 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 255 4 0 16 32 255 255), good := (rows 243 194 198 194 210 226 194 194) }] }

theorem profile17_node6 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,192] 6 217 profile17_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56,192] 6 217 profile17_node6_cert).mp (by decide +kernel))

def profile17_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile17_node1_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile17_node1 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [56] 6 (by decide) (choices 2) [9,24,65,72,192] profile17_node1_route profile17_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile17_node2
  · exact profile17_node3
  · exact profile17_node4
  · exact profile17_node5
  · exact profile17_node6

def profile17_node8_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 89 11 244 248 240 240 64 128), lower := (rows 89 11 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 247 244 244 244 244 244 244) }] }

theorem profile17_node8 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,9] 6 240 profile17_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,9] 6 240 profile17_node8_cert).mp (by decide +kernel))

def profile17_node9_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 89 26 229 233 241 225 64 128), lower := (rows 89 26 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 255 255), good := (rows 245 210 196 192 208 224 192 192) }] }

theorem profile17_node9 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,24] 6 225 profile17_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,24] 6 225 profile17_node9_cert).mp (by decide +kernel))

def profile17_node11_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 89 35 28 200 208 224 64 128), lower := (rows 89 35 28 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) }] }

theorem profile17_node11 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,24] 6 192 profile17_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,24] 6 192 profile17_node11_cert).mp (by decide +kernel))

def profile17_node12_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 89 35 76 152 144 176 64 128), lower := (rows 89 35 76 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) }] }

theorem profile17_node12 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,72] 6 144 profile17_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,72] 6 144 profile17_node12_cert).mp (by decide +kernel))

def profile17_node13_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 89 35 140 216 208 240 64 128), lower := (rows 89 35 140 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) }] }

theorem profile17_node13 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,136] 6 208 profile17_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,136] 6 208 profile17_node13_cert).mp (by decide +kernel))

def profile17_node14_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 89 35 196 152 152 184 64 128), lower := (rows 89 35 196 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 16 32 255 255), good := (rows 213 231 196 196 212 228 196 196) }] }

theorem profile17_node14 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,192] 6 152 profile17_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33,192] 6 152 profile17_node14_cert).mp (by decide +kernel))

def profile17_node10_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile17_node10_route : Route 8 := (fun mask => match mask with | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile17_node10 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,33] 6 (by decide) (choices 2) [24,72,136,192] profile17_node10_route profile17_node10_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile17_node11
  · exact profile17_node12
  · exact profile17_node13
  · exact profile17_node14

def profile17_node15_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 89 42 213 217 209 241 64 128), lower := (rows 89 42 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 255 255), good := (rows 245 226 196 192 208 224 192 192) }] }

theorem profile17_node15 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,40] 6 209 profile17_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,40] 6 209 profile17_node15_cert).mp (by decide +kernel))

def profile17_node16_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 89 67 188 184 184 184 64 128), lower := (rows 89 67 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 255 255), good := (rows 211 195 196 192 208 224 192 192) }] }

theorem profile17_node16 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,65] 6 184 profile17_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,65] 6 184 profile17_node16_cert).mp (by decide +kernel))

def profile17_node17_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 89 74 181 185 177 177 64 128), lower := (rows 89 74 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 255 255), good := (rows 245 194 196 192 208 224 192 192) }] }

theorem profile17_node17 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,72] 6 177 profile17_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,72] 6 177 profile17_node17_cert).mp (by decide +kernel))

def profile17_node18_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 89 98 157 153 153 185 64 128), lower := (rows 89 98 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 255 255), good := (rows 209 226 196 192 208 226 192 192) }] }

theorem profile17_node18 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,96] 6 153 profile17_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,96] 6 153 profile17_node18_cert).mp (by decide +kernel))

def profile17_node19_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 89 131 252 248 248 248 64 128), lower := (rows 89 131 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 255 255), good := (rows 211 195 196 192 208 224 192 192) }] }

theorem profile17_node19 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,129] 6 248 profile17_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,129] 6 248 profile17_node19_cert).mp (by decide +kernel))

def profile17_node20_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 89 138 245 249 241 241 64 128), lower := (rows 89 138 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 255 255), good := (rows 245 194 196 192 208 224 192 192) }] }

theorem profile17_node20 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,136] 6 241 profile17_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,136] 6 241 profile17_node20_cert).mp (by decide +kernel))

def profile17_node21_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 89 162 221 217 217 249 64 128), lower := (rows 89 162 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 255 255), good := (rows 209 226 196 192 208 226 192 192) }] }

theorem profile17_node21 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,160] 6 217 profile17_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,160] 6 217 profile17_node21_cert).mp (by decide +kernel))

def profile17_node22_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 89 194 189 185 185 185 64 128), lower := (rows 89 194 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 255 4 0 16 32 255 255), good := (rows 211 194 198 194 210 226 194 194) }] }

theorem profile17_node22 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,192] 6 185 profile17_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88,192] 6 185 profile17_node22_cert).mp (by decide +kernel))

def profile17_node7_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile17_node7_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile17_node7 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [88] 6 (by decide) (choices 2) [9,24,33,40,65,72,96,129,136,160,192] profile17_node7_route profile17_node7_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile17_node8
  · exact profile17_node9
  · exact profile17_node10
  · exact profile17_node15
  · exact profile17_node16
  · exact profile17_node17
  · exact profile17_node18
  · exact profile17_node19
  · exact profile17_node20
  · exact profile17_node21
  · exact profile17_node22

def profile17_node24_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 105 11 212 216 208 240 64 128), lower := (rows 105 11 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 255 255 255 255), good := (rows 245 247 244 244 244 244 244 244) }] }

theorem profile17_node24 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,9] 6 208 profile17_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,9] 6 208 profile17_node24_cert).mp (by decide +kernel))

def profile17_node26_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 105 19 28 200 208 224 64 128), lower := (rows 105 19 28 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) }] }

theorem profile17_node26 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,24] 6 192 profile17_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,24] 6 192 profile17_node26_cert).mp (by decide +kernel))

def profile17_node27_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 105 19 76 152 144 176 64 128), lower := (rows 105 19 76 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) }] }

theorem profile17_node27 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,72] 6 144 profile17_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,72] 6 144 profile17_node27_cert).mp (by decide +kernel))

def profile17_node28_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 105 19 84 136 152 168 64 128), lower := (rows 105 19 84 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 22 0 16 32 255 255), good := (rows 225 215 212 192 212 224 192 192) }] }

theorem profile17_node28 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,80] 6 136 profile17_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,80] 6 136 profile17_node28_cert).mp (by decide +kernel))

def profile17_node29_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 105 19 140 216 208 240 64 128), lower := (rows 105 19 140 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 244 240 240 240 240 240) }] }

theorem profile17_node29 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,136] 6 208 profile17_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,136] 6 208 profile17_node29_cert).mp (by decide +kernel))

def profile17_node30_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 105 19 148 200 216 232 64 128), lower := (rows 105 19 148 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 22 0 16 32 255 255), good := (rows 225 215 212 192 212 224 192 192) }] }

theorem profile17_node30 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,144] 6 200 profile17_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,144] 6 200 profile17_node30_cert).mp (by decide +kernel))

def profile17_node31_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 105 19 196 152 152 184 64 128), lower := (rows 105 19 196 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 255 0 16 32 255 255), good := (rows 229 215 196 196 212 228 196 196) }] }

theorem profile17_node31 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,192] 6 152 profile17_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17,192] 6 152 profile17_node31_cert).mp (by decide +kernel))

def profile17_node25_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile17_node25_route : Route 8 := (fun mask => (mask,id))

theorem profile17_node25 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,17] 6 (by decide) (choices 2) [24,72,80,136,144,192] profile17_node25_route profile17_node25_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile17_node26
  · exact profile17_node27
  · exact profile17_node28
  · exact profile17_node29
  · exact profile17_node30
  · exact profile17_node31

def profile17_node32_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 105 26 213 217 209 241 64 128), lower := (rows 105 26 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 255 255), good := (rows 245 210 196 192 208 224 192 192) }] }

theorem profile17_node32 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,24] 6 209 profile17_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,24] 6 209 profile17_node32_cert).mp (by decide +kernel))

def profile17_node33_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 105 67 156 152 152 184 64 128), lower := (rows 105 67 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 255 255), good := (rows 227 195 196 192 208 224 192 192) }] }

theorem profile17_node33 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,65] 6 152 profile17_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,65] 6 152 profile17_node33_cert).mp (by decide +kernel))

def profile17_node34_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 105 74 149 153 145 177 64 128), lower := (rows 105 74 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 255 255), good := (rows 245 194 196 192 208 224 192 192) }] }

theorem profile17_node34 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,72] 6 145 profile17_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,72] 6 145 profile17_node34_cert).mp (by decide +kernel))

def profile17_node35_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 105 82 157 153 153 185 64 128), lower := (rows 105 82 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 18 4 0 16 32 255 255), good := (rows 225 210 196 192 210 224 192 192) }] }

theorem profile17_node35 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,80] 6 153 profile17_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,80] 6 153 profile17_node35_cert).mp (by decide +kernel))

def profile17_node36_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 105 131 220 216 216 248 64 128), lower := (rows 105 131 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 255 255), good := (rows 227 195 196 192 208 224 192 192) }] }

theorem profile17_node36 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,129] 6 216 profile17_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,129] 6 216 profile17_node36_cert).mp (by decide +kernel))

def profile17_node37_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 105 138 213 217 209 241 64 128), lower := (rows 105 138 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 255 255), good := (rows 245 194 196 192 208 224 192 192) }] }

theorem profile17_node37 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,136] 6 209 profile17_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,136] 6 209 profile17_node37_cert).mp (by decide +kernel))

def profile17_node38_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 105 146 221 217 217 249 64 128), lower := (rows 105 146 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 18 4 0 16 32 255 255), good := (rows 225 210 196 192 210 224 192 192) }] }

theorem profile17_node38 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,144] 6 217 profile17_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,144] 6 217 profile17_node38_cert).mp (by decide +kernel))

def profile17_node39_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 105 194 157 153 153 185 64 128), lower := (rows 105 194 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 255 4 0 16 32 255 255), good := (rows 227 194 198 194 210 226 194 194) }] }

theorem profile17_node39 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,192] 6 153 profile17_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104,192] 6 153 profile17_node39_cert).mp (by decide +kernel))

def profile17_node23_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile17_node23_route : Route 8 := (fun mask => (mask,id))

theorem profile17_node23 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [104] 6 (by decide) (choices 2) [9,17,24,65,72,80,129,136,144,192] profile17_node23_route profile17_node23_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile17_node24
  · exact profile17_node25
  · exact profile17_node32
  · exact profile17_node33
  · exact profile17_node34
  · exact profile17_node35
  · exact profile17_node36
  · exact profile17_node37
  · exact profile17_node38
  · exact profile17_node39

def profile17_node40_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 201 251 253 249 249 249 64 128), lower := (rows 201 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 9 2 4 8 0 32 255 255), good := (rows 201 194 196 201 192 224 192 192) }] }

theorem profile17_node40 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [200] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [200] 6 249 profile17_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [200] 6 249 profile17_node40_cert).mp (by decide +kernel))

def profile17_node41_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 225 219 221 217 217 249 64 128), lower := (rows 225 2 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 33 2 4 0 16 32 255 255), good := (rows 225 194 196 192 208 225 192 192) }] }

theorem profile17_node41 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [224] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [224] 6 217 profile17_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [224] 6 217 profile17_node41_cert).mp (by decide +kernel))

def profile17_node0_column : Nat → Fin 8 := fun mask => match mask with | 14 => 1 | 22 => 1 | 38 => 1 | 70 => 1 | 134 => 1 | 26 => 1 | 42 => 1 | 74 => 1 | 138 => 1 | 50 => 1 | 82 => 1 | 146 => 1 | 98 => 1 | 162 => 1 | 194 => 1 | 28 => 2 | 44 => 2 | 76 => 2 | 140 => 2 | 52 => 2 | 84 => 2 | 148 => 2 | 100 => 2 | 164 => 2 | 196 => 2 | _ => 0

def profile17_node0_route : Route 8 := (fun mask => match mask with | 152 => (88,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 168 => (104,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 112 => (104,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 176 => (104,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 208 => (200,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile17_node0 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [] 6 (by decide) (choices 3) [56,88,104,200,224] profile17_node0_route profile17_node0_column
    (by change RowCover 8 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile17_node1
  · exact profile17_node7
  · exact profile17_node23
  · exact profile17_node40
  · exact profile17_node41

theorem profile17 : Upper (D (n:=8) [49,32,32,18,18,17,2,2]) (R (n:=8) [49,32,32,18,18,17,2,2]) [] 6 := profile17_node0


#print axioms profile17
end Delivery.SmallBudgetTenFinite8
