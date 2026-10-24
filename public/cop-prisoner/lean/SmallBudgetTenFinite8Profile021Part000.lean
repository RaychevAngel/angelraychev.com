import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile21_node2_cert : CutBound 8 := { lost := (rows 0 192 0 0 0 0 0 0), upper := (rows 49 19 213 217 209 241 64 128), lower := (rows 49 19 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 179 147 132 136 144 160 128 128) },{ target := 7, region := (rows 1 3 4 8 16 32 255 0), good := (rows 115 83 68 72 80 96 64 64) }] }

theorem profile21_node2 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,17] 6 209 profile21_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,17] 6 209 profile21_node2_cert).mp (by decide +kernel))

def profile21_node3_cert : CutBound 8 := { lost := (rows 0 144 0 0 0 0 0 0), upper := (rows 49 67 213 217 209 241 64 128), lower := (rows 49 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 227 195 196 200 192 224 192 192) },{ target := 7, region := (rows 1 3 4 8 16 32 255 0), good := (rows 115 67 68 72 80 96 64 64) }] }

theorem profile21_node3 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,65] 6 209 profile21_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,65] 6 209 profile21_node3_cert).mp (by decide +kernel))

def profile21_node4_cert : CutBound 8 := { lost := (rows 0 129 0 0 0 0 0 0), upper := (rows 49 82 213 217 209 241 64 128), lower := (rows 49 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 242 210 196 200 210 224 192 192) },{ target := 7, region := (rows 1 19 4 8 16 32 255 0), good := (rows 115 82 68 72 82 96 64 64) }] }

theorem profile21_node4 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,80] 6 209 profile21_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,80] 6 209 profile21_node4_cert).mp (by decide +kernel))

def profile21_node5_cert : CutBound 8 := { lost := (rows 0 17 0 0 0 0 0 0), upper := (rows 49 194 213 217 209 241 64 128), lower := (rows 49 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 242 194 198 202 210 226 194 194) },{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 227 194 198 202 194 226 194 194) }] }

theorem profile21_node5 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,192] 6 209 profile21_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48,192] 6 209 profile21_node5_cert).mp (by decide +kernel))

def profile21_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile21_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile21_node1 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [48] 6 (by decide) (choices 2) [17,65,80,192] profile21_node1_route profile21_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node2
  · exact profile21_node3
  · exact profile21_node4
  · exact profile21_node5

def profile21_node7_cert : CutBound 8 := { lost := (rows 128 192 0 0 0 0 0 0), upper := (rows 81 19 245 249 241 241 64 128), lower := (rows 81 19 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 147 147 132 136 144 160 128 128) },{ target := 7, region := (rows 19 19 4 8 16 32 255 0), good := (rows 83 83 68 72 83 96 64 64) }] }

theorem profile21_node7 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,17] 6 241 profile21_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,17] 6 241 profile21_node7_cert).mp (by decide +kernel))

def profile21_node9_cert : CutBound 8 := { lost := (rows 0 0 64 1 0 0 0 0), upper := (rows 81 35 21 216 208 240 64 128), lower := (rows 81 35 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 149 167 149 136 144 160 128 128) }] }

theorem profile21_node9 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,17] 6 208 profile21_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,17] 6 208 profile21_node9_cert).mp (by decide +kernel))

def profile21_node10_cert : CutBound 8 := { lost := (rows 0 0 16 1 0 0 0 0), upper := (rows 81 35 69 152 144 176 64 128), lower := (rows 81 35 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 2 7 8 0 32 255 255), good := (rows 197 231 197 200 192 224 192 192) }] }

theorem profile21_node10 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,65] 6 144 profile21_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,65] 6 144 profile21_node10_cert).mp (by decide +kernel))

def profile21_node11_cert : CutBound 8 := { lost := (rows 0 64 1 64 0 0 0 0), upper := (rows 81 35 84 153 145 177 64 128), lower := (rows 81 35 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 212 230 212 200 212 224 192 192) },{ target := 6, region := (rows 1 3 4 11 19 35 0 255), good := (rows 187 187 148 136 144 160 128 128) }] }

theorem profile21_node11 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,80] 6 145 profile21_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,80] 6 145 profile21_node11_cert).mp (by decide +kernel))

def profile21_node12_cert : CutBound 8 := { lost := (rows 0 0 16 1 0 0 0 0), upper := (rows 81 35 133 216 208 240 64 128), lower := (rows 81 35 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 1 2 7 8 0 32 255 255), good := (rows 197 231 197 200 192 224 192 192) }] }

theorem profile21_node12 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,129] 6 208 profile21_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,129] 6 208 profile21_node12_cert).mp (by decide +kernel))

def profile21_node13_cert : CutBound 8 := { lost := (rows 0 0 65 0 0 0 0 0), upper := (rows 81 35 148 217 209 241 64 128), lower := (rows 81 35 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 212 230 212 200 212 224 192 192) },{ target := 6, region := (rows 1 2 21 8 16 32 0 255), good := (rows 149 167 148 136 148 160 128 128) }] }

theorem profile21_node13 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,144] 6 209 profile21_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,144] 6 209 profile21_node13_cert).mp (by decide +kernel))

def profile21_node14_cert : CutBound 8 := { lost := (rows 0 0 17 0 0 0 0 0), upper := (rows 81 35 196 153 145 177 64 128), lower := (rows 81 35 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 212 230 196 204 212 228 196 196) },{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 231 196 204 196 228 196 196) }] }

theorem profile21_node14 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,192] 6 145 profile21_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33,192] 6 145 profile21_node14_cert).mp (by decide +kernel))

def profile21_node8_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile21_node8_route : Route 8 := (fun mask => (mask,id))

theorem profile21_node8 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,33] 6 (by decide) (choices 2) [17,65,80,129,144,192] profile21_node8_route profile21_node8_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node9
  · exact profile21_node10
  · exact profile21_node11
  · exact profile21_node12
  · exact profile21_node13
  · exact profile21_node14

def profile21_node16_cert : CutBound 8 := { lost := (rows 0 0 64 16 0 0 0 0), upper := (rows 81 50 21 201 209 225 64 128), lower := (rows 81 50 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 13 0 37 255 255), good := (rows 233 226 237 200 192 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 149 178 149 136 144 160 128 128) }] }

theorem profile21_node16 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,17] 6 193 profile21_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,17] 6 193 profile21_node16_cert).mp (by decide +kernel))

def profile21_node17_cert : CutBound 8 := { lost := (rows 0 64 16 64 0 0 0 0), upper := (rows 81 50 69 153 145 177 64 128), lower := (rows 81 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 197 226 197 200 192 224 192 192) },{ target := 6, region := (rows 1 7 4 13 21 37 0 255), good := (rows 187 178 191 136 144 160 128 128) }] }

theorem profile21_node17 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,65] 6 145 profile21_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,65] 6 145 profile21_node17_cert).mp (by decide +kernel))

def profile21_node18_cert : CutBound 8 := { lost := (rows 0 0 1 16 0 0 0 0), upper := (rows 81 50 84 137 145 161 64 128), lower := (rows 81 50 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 23 8 16 32 255 255), good := (rows 212 246 212 200 212 224 192 192) },{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 233 226 196 200 192 224 192 192) }] }

theorem profile21_node18 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,80] 6 129 profile21_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,80] 6 129 profile21_node18_cert).mp (by decide +kernel))

def profile21_node19_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 81 50 133 217 209 241 64 128), lower := (rows 81 50 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 197 226 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 149 178 133 136 144 160 128 128) }] }

theorem profile21_node19 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,129] 6 209 profile21_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,129] 6 209 profile21_node19_cert).mp (by decide +kernel))

def profile21_node20_cert : CutBound 8 := { lost := (rows 0 0 1 16 0 0 0 0), upper := (rows 81 50 148 201 209 225 64 128), lower := (rows 81 50 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 23 8 16 32 255 255), good := (rows 212 246 212 200 212 224 192 192) },{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 233 226 196 200 192 224 192 192) }] }

theorem profile21_node20 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,144] 6 193 profile21_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,144] 6 193 profile21_node20_cert).mp (by decide +kernel))

def profile21_node21_cert : CutBound 8 := { lost := (rows 0 0 17 0 0 0 0 0), upper := (rows 81 50 196 153 145 177 64 128), lower := (rows 81 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 212 246 196 204 212 228 196 196) },{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 230 196 204 196 228 196 196) }] }

theorem profile21_node21 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,192] 6 145 profile21_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48,192] 6 145 profile21_node21_cert).mp (by decide +kernel))

def profile21_node15_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile21_node15_route : Route 8 := (fun mask => (mask,id))

theorem profile21_node15 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,48] 6 (by decide) (choices 2) [17,65,80,129,144,192] profile21_node15_route profile21_node15_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node16
  · exact profile21_node17
  · exact profile21_node18
  · exact profile21_node19
  · exact profile21_node20
  · exact profile21_node21

def profile21_node22_cert : CutBound 8 := { lost := (rows 0 16 64 64 0 0 0 0), upper := (rows 81 67 181 185 177 177 64 128), lower := (rows 81 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 6, region := (rows 1 2 7 11 19 35 0 255), good := (rows 189 191 132 136 144 160 128 128) }] }

theorem profile21_node22 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,65] 6 177 profile21_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,65] 6 177 profile21_node22_cert).mp (by decide +kernel))

def profile21_node23_cert : CutBound 8 := { lost := (rows 0 1 64 64 0 0 0 0), upper := (rows 81 82 181 185 177 177 64 128), lower := (rows 81 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 210 210 196 200 210 224 192 192) },{ target := 6, region := (rows 1 2 5 9 17 33 0 255), good := (rows 189 146 132 136 144 160 128 128) }] }

theorem profile21_node23 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,80] 6 177 profile21_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,80] 6 177 profile21_node23_cert).mp (by decide +kernel))

def profile21_node24_cert : CutBound 8 := { lost := (rows 0 17 0 0 0 0 0 0), upper := (rows 81 98 149 153 145 177 64 128), lower := (rows 81 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 208 226 196 200 208 226 192 192) },{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) }] }

theorem profile21_node24 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,96] 6 145 profile21_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,96] 6 145 profile21_node24_cert).mp (by decide +kernel))

def profile21_node25_cert : CutBound 8 := { lost := (rows 0 80 0 0 0 0 0 0), upper := (rows 81 131 245 249 241 241 64 128), lower := (rows 81 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 147 131 132 136 144 160 128 128) }] }

theorem profile21_node25 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,129] 6 241 profile21_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,129] 6 241 profile21_node25_cert).mp (by decide +kernel))

def profile21_node26_cert : CutBound 8 := { lost := (rows 0 65 0 0 0 0 0 0), upper := (rows 81 146 245 249 241 241 64 128), lower := (rows 81 146 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 210 210 196 200 210 224 192 192) },{ target := 6, region := (rows 1 19 4 8 16 32 0 255), good := (rows 147 146 132 136 146 160 128 128) }] }

theorem profile21_node26 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,144] 6 241 profile21_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,144] 6 241 profile21_node26_cert).mp (by decide +kernel))

def profile21_node27_cert : CutBound 8 := { lost := (rows 0 17 0 0 0 0 0 0), upper := (rows 81 162 213 217 209 241 64 128), lower := (rows 81 162 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 208 226 196 200 208 226 192 192) },{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) }] }

theorem profile21_node27 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,160] 6 209 profile21_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,160] 6 209 profile21_node27_cert).mp (by decide +kernel))

def profile21_node28_cert : CutBound 8 := { lost := (rows 0 17 0 0 0 0 0 0), upper := (rows 81 194 181 185 177 177 64 128), lower := (rows 81 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 210 194 198 202 210 226 194 194) },{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 195 194 198 202 194 226 194 194) }] }

theorem profile21_node28 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,192] 6 177 profile21_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80,192] 6 177 profile21_node28_cert).mp (by decide +kernel))

def profile21_node6_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile21_node6_route : Route 8 := (fun mask => (mask,id))

theorem profile21_node6 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [80] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile21_node6_route profile21_node6_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node7
  · exact profile21_node8
  · exact profile21_node15
  · exact profile21_node22
  · exact profile21_node23
  · exact profile21_node24
  · exact profile21_node25
  · exact profile21_node26
  · exact profile21_node27
  · exact profile21_node28

def profile21_node29_cert : CutBound 8 := { lost := (rows 144 0 0 0 0 0 0 0), upper := (rows 97 211 213 217 209 241 64 128), lower := (rows 97 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 255 255), good := (rows 225 194 196 200 192 225 192 192) },{ target := 7, region := (rows 33 2 4 8 16 32 255 0), good := (rows 97 66 68 72 80 97 64 64) }] }

theorem profile21_node29 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [96] 6 209 profile21_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [96] 6 209 profile21_node29_cert).mp (by decide +kernel))

def profile21_node32_cert : CutBound 8 := { lost := (rows 16 0 0 1 0 0 0 0), upper := (rows 193 19 21 248 240 240 64 128), lower := (rows 193 19 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) }] }

theorem profile21_node32 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,17] 6 240 profile21_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,17] 6 240 profile21_node32_cert).mp (by decide +kernel))

def profile21_node33_cert : CutBound 8 := { lost := (rows 16 0 16 1 0 0 0 0), upper := (rows 193 19 37 216 208 240 64 128), lower := (rows 193 19 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 195 229 201 193 229 193 193) }] }

theorem profile21_node33 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,33] 6 208 profile21_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,33] 6 208 profile21_node33_cert).mp (by decide +kernel))

def profile21_node35_cert : CutBound 8 := { lost := (rows 16 0 1 0 0 0 0 0), upper := (rows 193 19 52 25 208 224 64 128), lower := (rows 193 19 52 25 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 255 255 255 255), good := (rows 244 246 244 252 244 244 244 244) },{ target := 4, region := (rows 255 2 4 8 0 255 255 255), good := (rows 225 227 229 233 225 225 225 225) }] }

theorem profile21_node35 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,17] 6 192 profile21_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,17] 6 192 profile21_node35_cert).mp (by decide +kernel))

def profile21_node36_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 193 19 52 73 144 176 64 128), lower := (rows 193 19 52 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 255 255 255 255), good := (rows 244 246 244 252 244 244 244 244) },{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 203 237 201 201 233 201 201) }] }

theorem profile21_node36 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,65] 6 144 profile21_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,65] 6 144 profile21_node36_cert).mp (by decide +kernel))

def profile21_node37_cert : CutBound 8 := { lost := (rows 16 0 0 1 0 0 0 0), upper := (rows 193 19 52 88 145 161 64 128), lower := (rows 193 19 52 88 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 30 16 32 255 255), good := (rows 192 218 252 216 216 224 192 192) },{ target := 4, region := (rows 255 2 4 8 0 255 255 255), good := (rows 225 227 229 233 225 225 225 225) }] }

theorem profile21_node37 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,80] 6 129 profile21_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,80] 6 129 profile21_node37_cert).mp (by decide +kernel))

def profile21_node38_cert : CutBound 8 := { lost := (rows 16 0 0 17 0 0 0 0), upper := (rows 193 19 52 200 17 49 64 128), lower := (rows 193 19 52 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 218 252 200 216 232 200 200) },{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 203 237 201 201 233 201 201) }] }

theorem profile21_node38 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,192] 6 17 profile21_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48,192] 6 17 profile21_node38_cert).mp (by decide +kernel))

def profile21_node34_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile21_node34_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile21_node34 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,48] 6 (by decide) (choices 2) [17,65,80,192] profile21_node34_route profile21_node34_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node35
  · exact profile21_node36
  · exact profile21_node37
  · exact profile21_node38

def profile21_node39_cert : CutBound 8 := { lost := (rows 16 0 16 1 0 0 0 0), upper := (rows 193 19 69 184 176 176 64 128), lower := (rows 193 19 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 252 248 248 248 248 248) },{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) }] }

theorem profile21_node39 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,65] 6 176 profile21_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,65] 6 176 profile21_node39_cert).mp (by decide +kernel))

def profile21_node40_cert : CutBound 8 := { lost := (rows 16 0 1 0 0 0 0 0), upper := (rows 193 19 84 185 177 177 64 128), lower := (rows 193 19 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 192 214 212 200 212 224 192 192) },{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) }] }

theorem profile21_node40 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,80] 6 177 profile21_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,80] 6 177 profile21_node40_cert).mp (by decide +kernel))

def profile21_node41_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 19 100 153 145 177 64 128), lower := (rows 193 19 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 255 255), good := (rows 192 210 228 200 208 228 192 192) },{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 195 229 201 193 229 193 193) }] }

theorem profile21_node41 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,96] 6 145 profile21_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,96] 6 145 profile21_node41_cert).mp (by decide +kernel))

def profile21_node42_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 19 196 57 49 49 64 128), lower := (rows 193 19 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 214 196 204 212 228 196 196) },{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) }] }

theorem profile21_node42 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,192] 6 49 profile21_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17,192] 6 49 profile21_node42_cert).mp (by decide +kernel))

def profile21_node31_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile21_node31_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile21_node31 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,17] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile21_node31_route profile21_node31_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node32
  · exact profile21_node33
  · exact profile21_node34
  · exact profile21_node39
  · exact profile21_node40
  · exact profile21_node41
  · exact profile21_node42

def profile21_node43_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 35 213 217 209 241 64 128), lower := (rows 193 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 34 4 8 0 32 255 255), good := (rows 193 227 197 201 193 227 193 193) }] }

theorem profile21_node43 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,33] 6 209 profile21_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,33] 6 209 profile21_node43_cert).mp (by decide +kernel))

def profile21_node46_cert : CutBound 8 := { lost := (rows 16 1 0 0 0 0 0 0), upper := (rows 193 50 21 25 208 224 64 128), lower := (rows 193 50 21 25 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 4, region := (rows 255 2 4 8 0 255 255 255), good := (rows 225 227 229 233 225 225 225 225) }] }

theorem profile21_node46 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,17] 6 192 profile21_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,17] 6 192 profile21_node46_cert).mp (by decide +kernel))

def profile21_node47_cert : CutBound 8 := { lost := (rows 16 1 0 16 0 0 0 0), upper := (rows 193 50 21 73 144 176 64 128), lower := (rows 193 50 21 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 235 205 201 201 233 201 201) }] }

theorem profile21_node47 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,65] 6 144 profile21_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,65] 6 144 profile21_node47_cert).mp (by decide +kernel))

def profile21_node48_cert : CutBound 8 := { lost := (rows 16 0 0 1 0 0 0 0), upper := (rows 193 50 21 88 145 161 64 128), lower := (rows 193 50 21 88 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 30 16 32 255 255), good := (rows 192 250 220 216 216 224 192 192) },{ target := 4, region := (rows 255 2 4 8 0 255 255 255), good := (rows 225 227 229 233 225 225 225 225) }] }

theorem profile21_node48 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,80] 6 129 profile21_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,80] 6 129 profile21_node48_cert).mp (by decide +kernel))

def profile21_node49_cert : CutBound 8 := { lost := (rows 16 0 0 17 0 0 0 0), upper := (rows 193 50 21 200 17 49 64 128), lower := (rows 193 50 21 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 250 220 200 216 232 200 200) },{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 235 205 201 201 233 201 201) }] }

theorem profile21_node49 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,192] 6 17 profile21_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17,192] 6 17 profile21_node49_cert).mp (by decide +kernel))

def profile21_node45_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile21_node45_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile21_node45 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,17] 6 (by decide) (choices 2) [17,65,80,192] profile21_node45_route profile21_node45_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node46
  · exact profile21_node47
  · exact profile21_node48
  · exact profile21_node49

def profile21_node50_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 50 69 153 145 177 64 128), lower := (rows 193 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) }] }

theorem profile21_node50 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,65] 6 145 profile21_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,65] 6 145 profile21_node50_cert).mp (by decide +kernel))

def profile21_node51_cert : CutBound 8 := { lost := (rows 16 0 1 0 0 0 0 0), upper := (rows 193 50 84 153 145 177 64 128), lower := (rows 193 50 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 192 246 212 200 212 224 192 192) },{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 227 197 201 193 225 193 193) }] }

theorem profile21_node51 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,80] 6 145 profile21_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,80] 6 145 profile21_node51_cert).mp (by decide +kernel))

def profile21_node52_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 50 196 25 17 49 64 128), lower := (rows 193 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 246 196 204 212 228 196 196) },{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) }] }

theorem profile21_node52 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,192] 6 17 profile21_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48,192] 6 17 profile21_node52_cert).mp (by decide +kernel))

def profile21_node44_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile21_node44_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile21_node44 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,48] 6 (by decide) (choices 2) [17,65,80,192] profile21_node44_route profile21_node44_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node45
  · exact profile21_node50
  · exact profile21_node51
  · exact profile21_node52

def profile21_node53_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 67 181 185 177 177 64 128), lower := (rows 193 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) }] }

theorem profile21_node53 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,65] 6 177 profile21_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,65] 6 177 profile21_node53_cert).mp (by decide +kernel))

def profile21_node54_cert : CutBound 8 := { lost := (rows 16 1 0 0 0 0 0 0), upper := (rows 193 82 181 185 177 177 64 128), lower := (rows 193 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 192 210 196 200 210 224 192 192) },{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) }] }

theorem profile21_node54 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,80] 6 177 profile21_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,80] 6 177 profile21_node54_cert).mp (by decide +kernel))

def profile21_node55_cert : CutBound 8 := { lost := (rows 16 17 0 0 0 0 0 0), upper := (rows 193 98 149 153 145 177 64 128), lower := (rows 193 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 192 226 196 200 208 226 192 192) },{ target := 4, region := (rows 255 34 4 8 0 32 255 255), good := (rows 193 227 197 201 193 227 193 193) }] }

theorem profile21_node55 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,96] 6 145 profile21_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,96] 6 145 profile21_node55_cert).mp (by decide +kernel))

def profile21_node56_cert : CutBound 8 := { lost := (rows 16 17 0 0 0 0 0 0), upper := (rows 193 194 53 57 49 49 64 128), lower := (rows 193 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 194 194 198 202 210 226 194 194) },{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) }] }

theorem profile21_node56 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,192] 6 49 profile21_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192,192] 6 49 profile21_node56_cert).mp (by decide +kernel))

def profile21_node30_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile21_node30_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile21_node30 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [192] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile21_node30_route profile21_node30_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node31
  · exact profile21_node43
  · exact profile21_node44
  · exact profile21_node53
  · exact profile21_node54
  · exact profile21_node55
  · exact profile21_node56

def profile21_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile21_node0_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile21_node0 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [] 6 (by decide) (choices 2) [48,80,96,192] profile21_node0_route profile21_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node1
  · exact profile21_node6
  · exact profile21_node29
  · exact profile21_node30

theorem profile21 : Upper (D (n:=8) [34,32,32,32,19,17,2,2]) (R (n:=8) [34,32,32,32,19,17,2,2]) [] 6 := profile21_node0


#print axioms profile21
end Delivery.SmallBudgetTenFinite8
