import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile5_node2_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 51 35 198 202 210 32 64 128), lower := (rows 51 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 255 255), good := (rows 223 223 196 200 208 192 192 192) }] }

theorem profile5_node2 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,33] 6 194 profile5_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,33] 6 194 profile5_node2_cert).mp (by decide +kernel))

def profile5_node3_cert : CutBound 8 := { lost := (rows 128 160 0 0 0 0 0 0), upper := (rows 51 67 230 234 242 32 64 128), lower := (rows 51 67 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 195 196 200 208 192 192 192) },{ target := 7, region := (rows 17 19 4 8 16 255 255 0), good := (rows 115 99 100 104 115 96 96 96) }] }

theorem profile5_node3 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,65] 6 226 profile5_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,65] 6 226 profile5_node3_cert).mp (by decide +kernel))

def profile5_node4_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 51 98 199 203 211 32 64 128), lower := (rows 51 98 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile5_node4 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,96] 6 195 profile5_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,96] 6 195 profile5_node4_cert).mp (by decide +kernel))

def profile5_node6_cert : CutBound 8 := { lost := (rows 0 32 32 2 0 0 0 0), upper := (rows 51 194 7 232 240 32 64 128), lower := (rows 51 194 7 8 16 32 64 128), losses := [{ target := 1, region := (rows 1 0 4 255 255 255 255 255), good := (rows 249 248 253 248 248 248 248 248) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 215 194 199 202 210 194 194 194) }] }

theorem profile5_node6 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,3] 6 224 profile5_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,3] 6 224 profile5_node6_cert).mp (by decide +kernel))

def profile5_node7_cert : CutBound 8 := { lost := (rows 0 32 2 32 0 0 0 0), upper := (rows 51 194 37 202 210 32 64 128), lower := (rows 51 194 37 8 16 32 64 128), losses := [{ target := 1, region := (rows 1 0 5 8 16 255 255 255), good := (rows 245 224 229 232 240 224 224 224) },{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 223 218 218 218 218 218) }] }

theorem profile5_node7 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,33] 6 194 profile5_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,33] 6 194 profile5_node7_cert).mp (by decide +kernel))

def profile5_node8_cert : CutBound 8 := { lost := (rows 0 32 0 34 0 0 0 0), upper := (rows 51 194 38 201 209 32 64 128), lower := (rows 51 194 38 8 16 32 64 128), losses := [{ target := 1, region := (rows 1 0 4 9 17 255 255 255), good := (rows 249 224 228 232 240 224 224 224) },{ target := 5, region := (rows 1 255 4 9 17 0 255 255), good := (rows 219 194 198 202 210 194 194 194) }] }

theorem profile5_node8 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,34] 6 193 profile5_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,34] 6 193 profile5_node8_cert).mp (by decide +kernel))

def profile5_node9_cert : CutBound 8 := { lost := (rows 0 32 34 0 0 0 0 0), upper := (rows 51 194 69 170 178 32 64 128), lower := (rows 51 194 69 8 16 32 64 128), losses := [{ target := 1, region := (rows 1 0 5 8 16 255 255 255), good := (rows 245 224 229 232 240 224 224 224) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 215 194 199 202 210 194 194 194) }] }

theorem profile5_node9 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,65] 6 162 profile5_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,65] 6 162 profile5_node9_cert).mp (by decide +kernel))

def profile5_node10_cert : CutBound 8 := { lost := (rows 0 32 32 2 0 0 0 0), upper := (rows 51 194 70 169 177 32 64 128), lower := (rows 51 194 70 8 16 32 64 128), losses := [{ target := 1, region := (rows 1 0 4 9 17 255 255 255), good := (rows 249 224 228 232 240 224 224 224) },{ target := 5, region := (rows 1 255 255 8 16 0 255 255), good := (rows 215 198 198 206 214 198 198 198) }] }

theorem profile5_node10 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,66] 6 161 profile5_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,66] 6 161 profile5_node10_cert).mp (by decide +kernel))

def profile5_node11_cert : CutBound 8 := { lost := (rows 0 32 2 32 0 0 0 0), upper := (rows 51 194 100 139 147 32 64 128), lower := (rows 51 194 100 8 16 32 64 128), losses := [{ target := 1, region := (rows 1 0 255 8 16 255 255 255), good := (rows 245 228 228 236 244 228 228 228) },{ target := 5, region := (rows 1 255 4 9 17 0 255 255), good := (rows 219 194 198 202 210 194 194 194) }] }

theorem profile5_node11 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,96] 6 131 profile5_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,96] 6 131 profile5_node11_cert).mp (by decide +kernel))

def profile5_node12_cert : CutBound 8 := { lost := (rows 0 32 34 0 0 0 0 0), upper := (rows 51 194 196 43 51 32 64 128), lower := (rows 51 194 196 8 16 32 64 128), losses := [{ target := 1, region := (rows 1 0 255 8 16 255 255 255), good := (rows 245 228 228 236 244 228 228 228) },{ target := 5, region := (rows 1 255 255 8 16 0 255 255), good := (rows 215 198 198 206 214 198 198 198) }] }

theorem profile5_node12 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,192] 6 35 profile5_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192,192] 6 35 profile5_node12_cert).mp (by decide +kernel))

def profile5_node5_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile5_node5_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile5_node5 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50,192] 6 (by decide) (choices 2) [3,33,34,65,66,96,192] profile5_node5_route profile5_node5_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node6
  · exact profile5_node7
  · exact profile5_node8
  · exact profile5_node9
  · exact profile5_node10
  · exact profile5_node11
  · exact profile5_node12

def profile5_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile5_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile5_node1 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [50] 6 (by decide) (choices 2) [33,65,96,192] profile5_node1_route profile5_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node2
  · exact profile5_node3
  · exact profile5_node4
  · exact profile5_node5

def profile5_node14_cert : CutBound 8 := { lost := (rows 128 128 0 0 0 0 0 0), upper := (rows 99 19 230 234 242 32 64 128), lower := (rows 99 19 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 19 18 4 8 16 255 255 0), good := (rows 99 115 100 104 115 96 96 96) }] }

theorem profile5_node14 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,17] 6 226 profile5_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,17] 6 226 profile5_node14_cert).mp (by decide +kernel))

def profile5_node15_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 99 35 214 218 210 32 64 128), lower := (rows 99 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 255 255), good := (rows 223 223 196 200 208 192 192 192) }] }

theorem profile5_node15 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,33] 6 210 profile5_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,33] 6 210 profile5_node15_cert).mp (by decide +kernel))

def profile5_node16_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 99 50 199 203 211 32 64 128), lower := (rows 99 50 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 210 196 200 208 192 192 192) }] }

theorem profile5_node16 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,48] 6 195 profile5_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,48] 6 195 profile5_node16_cert).mp (by decide +kernel))

def profile5_node17_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 99 98 151 155 147 32 64 128), lower := (rows 99 98 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile5_node17 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,96] 6 147 profile5_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,96] 6 147 profile5_node17_cert).mp (by decide +kernel))

def profile5_node18_cert : CutBound 8 := { lost := (rows 0 96 0 0 0 0 0 0), upper := (rows 99 131 246 250 242 32 64 128), lower := (rows 99 131 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) }] }

theorem profile5_node18 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,129] 6 242 profile5_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,129] 6 242 profile5_node18_cert).mp (by decide +kernel))

def profile5_node19_cert : CutBound 8 := { lost := (rows 0 96 0 0 0 0 0 0), upper := (rows 99 146 231 235 243 32 64 128), lower := (rows 99 146 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 255 255), good := (rows 195 210 196 200 210 192 192 192) },{ target := 6, region := (rows 1 18 4 8 16 255 0 255), good := (rows 163 178 164 168 178 160 160 160) }] }

theorem profile5_node19 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,144] 6 227 profile5_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,144] 6 227 profile5_node19_cert).mp (by decide +kernel))

def profile5_node20_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 99 162 215 219 211 32 64 128), lower := (rows 99 162 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile5_node20 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,160] 6 211 profile5_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98,160] 6 211 profile5_node20_cert).mp (by decide +kernel))

def profile5_node13_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile5_node13_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile5_node13 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [98] 6 (by decide) (choices 2) [17,33,48,96,129,144,160] profile5_node13_route profile5_node13_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node14
  · exact profile5_node15
  · exact profile5_node16
  · exact profile5_node17
  · exact profile5_node18
  · exact profile5_node19
  · exact profile5_node20

def profile5_node21_cert : CutBound 8 := { lost := (rows 130 0 0 0 0 0 0 0), upper := (rows 113 227 231 235 243 32 64 128), lower := (rows 113 2 4 8 16 32 64 128), losses := [{ target := 1, region := (rows 17 0 4 8 16 255 255 255), good := (rows 241 224 228 232 241 224 224 224) },{ target := 7, region := (rows 17 2 4 8 16 255 255 0), good := (rows 113 98 100 104 113 96 96 96) }] }

theorem profile5_node21 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [112] 6 227 profile5_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [112] 6 227 profile5_node21_cert).mp (by decide +kernel))

def profile5_node24_cert : CutBound 8 := { lost := (rows 2 32 0 32 0 0 0 0), upper := (rows 225 19 38 202 210 32 64 128), lower := (rows 225 19 38 8 16 32 64 128), losses := [{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 241 229 233 241 225 225 225) },{ target := 5, region := (rows 1 3 4 15 23 0 255 255), good := (rows 219 219 222 200 208 192 192 192) }] }

theorem profile5_node24 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,17,34] 6 194 profile5_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,17,34] 6 194 profile5_node24_cert).mp (by decide +kernel))

def profile5_node25_cert : CutBound 8 := { lost := (rows 2 0 2 0 0 0 0 0), upper := (rows 225 19 100 138 146 32 64 128), lower := (rows 225 19 100 8 16 32 64 128), losses := [{ target := 1, region := (rows 255 0 255 8 16 255 255 255), good := (rows 229 245 229 237 245 229 229 229) }] }

theorem profile5_node25 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,17,96] 6 130 profile5_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,17,96] 6 130 profile5_node25_cert).mp (by decide +kernel))

def profile5_node23_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile5_node23_route : Route 8 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile5_node23 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,17] 6 (by decide) (choices 2) [34,96] profile5_node23_route profile5_node23_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node24
  · exact profile5_node25

def profile5_node26_cert : CutBound 8 := { lost := (rows 2 0 32 32 0 0 0 0), upper := (rows 225 35 214 218 210 32 64 128), lower := (rows 225 35 4 8 16 32 64 128), losses := [{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 225 229 233 241 225 225 225) },{ target := 5, region := (rows 1 2 6 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) }] }

theorem profile5_node26 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,33] 6 210 profile5_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,33] 6 210 profile5_node26_cert).mp (by decide +kernel))

def profile5_node27_cert : CutBound 8 := { lost := (rows 2 64 0 0 0 0 0 0), upper := (rows 225 50 199 203 211 32 64 128), lower := (rows 225 50 4 8 16 32 64 128), losses := [{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 241 229 233 241 225 225 225) },{ target := 6, region := (rows 1 18 4 8 16 255 0 255), good := (rows 161 178 164 168 178 160 160 160) }] }

theorem profile5_node27 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,48] 6 195 profile5_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,48] 6 195 profile5_node27_cert).mp (by decide +kernel))

def profile5_node28_cert : CutBound 8 := { lost := (rows 2 128 0 0 0 0 0 0), upper := (rows 225 98 151 155 147 32 64 128), lower := (rows 225 98 4 8 16 32 64 128), losses := [{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 225 229 233 241 225 225 225) },{ target := 7, region := (rows 1 255 4 8 16 255 255 0), good := (rows 99 98 102 106 114 98 98 98) }] }

theorem profile5_node28 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,96] 6 147 profile5_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224,96] 6 147 profile5_node28_cert).mp (by decide +kernel))

def profile5_node22_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile5_node22_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile5_node22 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [224] 6 (by decide) (choices 2) [17,33,48,96] profile5_node22_route profile5_node22_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node23
  · exact profile5_node26
  · exact profile5_node27
  · exact profile5_node28

def profile5_node0_column : Nat → Fin 8 := fun mask => match mask with | 14 => 2 | 22 => 2 | 38 => 2 | 70 => 2 | 134 => 2 | 26 => 3 | 42 => 3 | 74 => 3 | 138 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 140 => 2 | 52 => 2 | 84 => 2 | 148 => 2 | 100 => 2 | 164 => 2 | 196 => 2 | 56 => 3 | 88 => 3 | 152 => 3 | 104 => 3 | 168 => 3 | 200 => 3 | _ => 0

def profile5_node0_route : Route 8 := (fun mask => match mask with | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 146 => (50,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 162 => (98,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 194 => (98,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile5_node0 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [] 6 (by decide) (choices 3) [50,98,112,224] profile5_node0_route profile5_node0_column
    (by change RowCover 8 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node1
  · exact profile5_node13
  · exact profile5_node21
  · exact profile5_node22

theorem profile5 : Upper (D (n:=8) [49,34,32,32,17,2,2,2]) (R (n:=8) [49,34,32,32,17,2,2,2]) [] 6 := profile5_node0


#print axioms profile5
end Delivery.SmallBudgetTenFinite8
