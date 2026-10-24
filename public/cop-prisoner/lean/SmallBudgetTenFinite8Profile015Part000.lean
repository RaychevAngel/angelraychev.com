import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile15_node3_cert : CutBound 8 := { lost := (rows 0 0 0 3 0 0 0 0), upper := (rows 19 35 7 200 208 224 64 128), lower := (rows 19 35 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 250 250 254 248 248 248 248 248) },{ target := 1, region := (rows 1 0 4 255 255 255 255 255), good := (rows 249 249 253 248 248 248 248 248) }] }

theorem profile15_node3 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,3] 6 192 profile15_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,3] 6 192 profile15_node3_cert).mp (by decide +kernel))

def profile15_node4_cert : CutBound 8 := { lost := (rows 0 0 2 1 0 0 0 0), upper := (rows 19 35 69 202 210 226 64 128), lower := (rows 19 35 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 255 255), good := (rows 250 250 252 200 208 224 192 192) },{ target := 1, region := (rows 1 0 7 8 16 32 255 255), good := (rows 213 229 197 200 208 224 192 192) }] }

theorem profile15_node4 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,65] 6 194 profile15_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,65] 6 194 profile15_node4_cert).mp (by decide +kernel))

def profile15_node5_cert : CutBound 8 := { lost := (rows 0 0 1 2 0 0 0 0), upper := (rows 19 35 70 201 209 225 64 128), lower := (rows 19 35 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 255 255), good := (rows 214 230 198 200 208 224 192 192) },{ target := 1, region := (rows 1 0 4 11 19 35 255 255), good := (rows 249 249 252 200 208 224 192 192) }] }

theorem profile15_node5 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,66] 6 193 profile15_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,66] 6 193 profile15_node5_cert).mp (by decide +kernel))

def profile15_node6_cert : CutBound 8 := { lost := (rows 0 0 3 0 0 0 0 0), upper := (rows 19 35 196 203 211 227 64 128), lower := (rows 19 35 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 214 230 196 204 212 228 196 196) },{ target := 1, region := (rows 1 0 255 8 16 32 255 255), good := (rows 213 229 196 204 212 228 196 196) }] }

theorem profile15_node6 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,192] 6 195 profile15_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33,192] 6 195 profile15_node6_cert).mp (by decide +kernel))

def profile15_node2_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile15_node2_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node2 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,33] 6 (by decide) (choices 2) [3,65,66,192] profile15_node2_route profile15_node2_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node3
  · exact profile15_node4
  · exact profile15_node5
  · exact profile15_node6

def profile15_node7_cert : CutBound 8 := { lost := (rows 128 128 0 0 0 0 0 0), upper := (rows 19 67 231 235 243 227 64 128), lower := (rows 19 67 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 17 19 4 8 16 32 255 0), good := (rows 83 67 68 72 83 96 64 64) }] }

theorem profile15_node7 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,65] 6 227 profile15_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,65] 6 227 profile15_node7_cert).mp (by decide +kernel))

def profile15_node8_cert : CutBound 8 := { lost := (rows 0 129 0 0 0 0 0 0), upper := (rows 19 98 199 203 211 227 64 128), lower := (rows 19 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 210 226 196 200 208 226 192 192) },{ target := 7, region := (rows 1 34 4 8 16 32 255 0), good := (rows 83 98 68 72 80 98 64 64) }] }

theorem profile15_node8 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,96] 6 195 profile15_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,96] 6 195 profile15_node8_cert).mp (by decide +kernel))

def profile15_node10_cert : CutBound 8 := { lost := (rows 0 1 0 2 0 0 0 0), upper := (rows 19 194 7 233 241 225 64 128), lower := (rows 19 194 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 210 194 198 202 210 226 194 194) },{ target := 1, region := (rows 1 0 4 13 21 37 255 255), good := (rows 249 192 253 200 208 224 192 192) }] }

theorem profile15_node10 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,3] 6 225 profile15_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,3] 6 225 profile15_node10_cert).mp (by decide +kernel))

def profile15_node12_cert : CutBound 8 := { lost := (rows 0 1 2 0 0 0 0 0), upper := (rows 19 194 37 11 208 224 64 128), lower := (rows 19 194 37 11 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 1, region := (rows 1 0 13 8 255 255 255 255), good := (rows 245 240 245 253 240 240 240 240) }] }

theorem profile15_node12 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,3] 6 192 profile15_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,3] 6 192 profile15_node12_cert).mp (by decide +kernel))

def profile15_node13_cert : CutBound 8 := { lost := (rows 0 1 0 2 0 0 0 0), upper := (rows 19 194 37 73 146 162 64 128), lower := (rows 19 194 37 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 1, region := (rows 1 0 4 13 16 32 255 255), good := (rows 217 192 237 201 208 224 192 192) }] }

theorem profile15_node13 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,65] 6 130 profile15_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,65] 6 130 profile15_node13_cert).mp (by decide +kernel))

def profile15_node14_cert : CutBound 8 := { lost := (rows 0 1 0 1 0 0 0 0), upper := (rows 19 194 37 74 145 161 64 128), lower := (rows 19 194 37 74 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 255 16 32 255 255), good := (rows 218 202 238 202 218 234 202 202) }] }

theorem profile15_node14 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,66] 6 129 profile15_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,66] 6 129 profile15_node14_cert).mp (by decide +kernel))

def profile15_node15_cert : CutBound 8 := { lost := (rows 0 1 0 1 0 0 0 0), upper := (rows 19 194 37 200 19 35 64 128), lower := (rows 19 194 37 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 255 16 32 255 255), good := (rows 218 202 238 202 218 234 202 202) }] }

theorem profile15_node15 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,192] 6 3 profile15_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33,192] 6 3 profile15_node15_cert).mp (by decide +kernel))

def profile15_node11_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile15_node11_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node11 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,33] 6 (by decide) (choices 2) [3,65,66,192] profile15_node11_route profile15_node11_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node12
  · exact profile15_node13
  · exact profile15_node14
  · exact profile15_node15

def profile15_node16_cert : CutBound 8 := { lost := (rows 0 1 1 0 0 0 0 0), upper := (rows 19 194 38 201 209 225 64 128), lower := (rows 19 194 38 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 36 8 16 32 255 255), good := (rows 210 194 230 202 210 230 194 194) }] }

theorem profile15_node16 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,34] 6 193 profile15_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,34] 6 193 profile15_node16_cert).mp (by decide +kernel))

def profile15_node17_cert : CutBound 8 := { lost := (rows 0 1 2 0 0 0 0 0), upper := (rows 19 194 69 171 179 163 64 128), lower := (rows 19 194 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 210 194 198 202 210 226 194 194) },{ target := 1, region := (rows 1 0 5 8 16 32 255 255), good := (rows 213 192 197 200 208 224 192 192) }] }

theorem profile15_node17 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,65] 6 163 profile15_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,65] 6 163 profile15_node17_cert).mp (by decide +kernel))

def profile15_node18_cert : CutBound 8 := { lost := (rows 0 1 1 0 0 0 0 0), upper := (rows 19 194 70 169 177 161 64 128), lower := (rows 19 194 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 32 255 255), good := (rows 214 198 198 206 214 230 198 198) }] }

theorem profile15_node18 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,66] 6 161 profile15_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,66] 6 161 profile15_node18_cert).mp (by decide +kernel))

def profile15_node19_cert : CutBound 8 := { lost := (rows 0 1 1 0 0 0 0 0), upper := (rows 19 194 100 139 147 163 64 128), lower := (rows 19 194 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 36 8 16 32 255 255), good := (rows 210 194 230 202 210 230 194 194) }] }

theorem profile15_node19 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,96] 6 131 profile15_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,96] 6 131 profile15_node19_cert).mp (by decide +kernel))

def profile15_node20_cert : CutBound 8 := { lost := (rows 0 1 1 0 0 0 0 0), upper := (rows 19 194 196 43 51 35 64 128), lower := (rows 19 194 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 32 255 255), good := (rows 214 198 198 206 214 230 198 198) }] }

theorem profile15_node20 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,192] 6 35 profile15_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192,192] 6 35 profile15_node20_cert).mp (by decide +kernel))

def profile15_node9_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile15_node9_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node9 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18,192] 6 (by decide) (choices 2) [3,33,34,65,66,96,192] profile15_node9_route profile15_node9_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile15_node10
  · exact profile15_node11
  · exact profile15_node16
  · exact profile15_node17
  · exact profile15_node18
  · exact profile15_node19
  · exact profile15_node20

def profile15_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile15_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node1 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [18] 6 (by decide) (choices 2) [33,65,96,192] profile15_node1_route profile15_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node2
  · exact profile15_node7
  · exact profile15_node8
  · exact profile15_node9

def profile15_node23_cert : CutBound 8 := { lost := (rows 0 0 64 1 0 0 0 0), upper := (rows 49 67 7 202 210 226 64 128), lower := (rows 49 67 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 255 255), good := (rows 240 250 254 200 208 224 192 192) },{ target := 6, region := (rows 1 2 6 8 16 32 0 255), good := (rows 177 135 135 136 144 160 128 128) }] }

theorem profile15_node23 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,3] 6 194 profile15_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,3] 6 194 profile15_node23_cert).mp (by decide +kernel))

def profile15_node24_cert : CutBound 8 := { lost := (rows 0 0 2 1 0 0 0 0), upper := (rows 49 67 69 138 146 162 64 128), lower := (rows 49 67 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 240 250 196 200 208 224 192 192) },{ target := 1, region := (rows 1 0 7 8 16 32 255 255), good := (rows 245 197 197 200 208 224 192 192) }] }

theorem profile15_node24 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,65] 6 130 profile15_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,65] 6 130 profile15_node24_cert).mp (by decide +kernel))

def profile15_node25_cert : CutBound 8 := { lost := (rows 64 0 1 64 0 0 0 0), upper := (rows 49 67 70 139 147 163 64 128), lower := (rows 49 67 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 240 198 198 200 208 224 192 192) },{ target := 6, region := (rows 7 2 4 14 22 38 0 255), good := (rows 177 187 191 136 144 160 128 128) }] }

theorem profile15_node25 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,66] 6 131 profile15_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,66] 6 131 profile15_node25_cert).mp (by decide +kernel))

def profile15_node26_cert : CutBound 8 := { lost := (rows 0 0 2 1 0 0 0 0), upper := (rows 49 67 133 202 210 226 64 128), lower := (rows 49 67 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 240 250 196 200 208 224 192 192) },{ target := 1, region := (rows 1 0 7 8 16 32 255 255), good := (rows 245 197 197 200 208 224 192 192) }] }

theorem profile15_node26 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,129] 6 194 profile15_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,129] 6 194 profile15_node26_cert).mp (by decide +kernel))

def profile15_node27_cert : CutBound 8 := { lost := (rows 0 0 65 0 0 0 0 0), upper := (rows 49 67 134 203 211 227 64 128), lower := (rows 49 67 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 240 198 198 200 208 224 192 192) },{ target := 6, region := (rows 1 2 6 8 16 32 0 255), good := (rows 177 135 134 136 144 160 128 128) }] }

theorem profile15_node27 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,130] 6 195 profile15_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,130] 6 195 profile15_node27_cert).mp (by decide +kernel))

def profile15_node28_cert : CutBound 8 := { lost := (rows 0 0 3 0 0 0 0 0), upper := (rows 49 67 196 139 147 163 64 128), lower := (rows 49 67 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 244 198 196 204 212 228 196 196) },{ target := 1, region := (rows 1 0 255 8 16 32 255 255), good := (rows 245 197 196 204 212 228 196 196) }] }

theorem profile15_node28 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,192] 6 131 profile15_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65,192] 6 131 profile15_node28_cert).mp (by decide +kernel))

def profile15_node22_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile15_node22_route : Route 8 := (fun mask => (mask,id))

theorem profile15_node22 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,65] 6 (by decide) (choices 2) [3,65,66,129,130,192] profile15_node22_route profile15_node22_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile15_node23
  · exact profile15_node24
  · exact profile15_node25
  · exact profile15_node26
  · exact profile15_node27
  · exact profile15_node28

def profile15_node31_cert : CutBound 8 := { lost := (rows 2 1 0 0 0 0 0 0), upper := (rows 49 194 7 11 208 224 64 128), lower := (rows 49 194 7 11 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 1, region := (rows 255 0 4 8 255 255 255 255), good := (rows 241 241 245 249 241 241 241 241) }] }

theorem profile15_node31 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,3] 6 192 profile15_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,3] 6 192 profile15_node31_cert).mp (by decide +kernel))

def profile15_node32_cert : CutBound 8 := { lost := (rows 0 1 0 2 0 0 0 0), upper := (rows 49 194 7 73 146 162 64 128), lower := (rows 49 194 7 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 1, region := (rows 1 0 4 13 16 32 255 255), good := (rows 249 192 205 201 208 224 192 192) }] }

theorem profile15_node32 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,65] 6 130 profile15_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,65] 6 130 profile15_node32_cert).mp (by decide +kernel))

def profile15_node33_cert : CutBound 8 := { lost := (rows 0 1 0 1 0 0 0 0), upper := (rows 49 194 7 74 145 161 64 128), lower := (rows 49 194 7 74 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 255 16 32 255 255), good := (rows 250 202 206 202 218 234 202 202) }] }

theorem profile15_node33 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,66] 6 129 profile15_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,66] 6 129 profile15_node33_cert).mp (by decide +kernel))

def profile15_node34_cert : CutBound 8 := { lost := (rows 0 1 0 1 0 0 0 0), upper := (rows 49 194 7 200 19 35 64 128), lower := (rows 49 194 7 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 255 16 32 255 255), good := (rows 250 202 206 202 218 234 202 202) }] }

theorem profile15_node34 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,192] 6 3 profile15_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3,192] 6 3 profile15_node34_cert).mp (by decide +kernel))

def profile15_node30_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile15_node30_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node30 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,3] 6 (by decide) (choices 2) [3,65,66,192] profile15_node30_route profile15_node30_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node31
  · exact profile15_node32
  · exact profile15_node33
  · exact profile15_node34

def profile15_node35_cert : CutBound 8 := { lost := (rows 0 1 2 0 0 0 0 0), upper := (rows 49 194 69 139 147 163 64 128), lower := (rows 49 194 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 242 194 198 202 210 226 194 194) },{ target := 1, region := (rows 1 0 5 8 16 32 255 255), good := (rows 245 192 197 200 208 224 192 192) }] }

theorem profile15_node35 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,65] 6 131 profile15_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,65] 6 131 profile15_node35_cert).mp (by decide +kernel))

def profile15_node36_cert : CutBound 8 := { lost := (rows 0 1 1 0 0 0 0 0), upper := (rows 49 194 70 139 147 163 64 128), lower := (rows 49 194 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 32 255 255), good := (rows 246 198 198 206 214 230 198 198) }] }

theorem profile15_node36 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,66] 6 131 profile15_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,66] 6 131 profile15_node36_cert).mp (by decide +kernel))

def profile15_node37_cert : CutBound 8 := { lost := (rows 0 1 1 0 0 0 0 0), upper := (rows 49 194 196 11 19 35 64 128), lower := (rows 49 194 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 32 255 255), good := (rows 246 198 198 206 214 230 198 198) }] }

theorem profile15_node37 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,192] 6 3 profile15_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192,192] 6 3 profile15_node37_cert).mp (by decide +kernel))

def profile15_node29_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile15_node29_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node29 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48,192] 6 (by decide) (choices 2) [3,65,66,192] profile15_node29_route profile15_node29_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node30
  · exact profile15_node35
  · exact profile15_node36
  · exact profile15_node37

def profile15_node21_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile15_node21_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node21 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [48] 6 (by decide) (choices 2) [65,192] profile15_node21_route profile15_node21_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile15_node22
  · exact profile15_node29

def profile15_node39_cert : CutBound 8 := { lost := (rows 128 128 0 0 0 0 0 0), upper := (rows 67 19 231 235 243 227 64 128), lower := (rows 67 19 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 19 18 4 8 16 32 255 0), good := (rows 67 83 68 72 83 96 64 64) }] }

theorem profile15_node39 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,17] 6 227 profile15_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,17] 6 227 profile15_node39_cert).mp (by decide +kernel))

def profile15_node41_cert : CutBound 8 := { lost := (rows 0 0 64 2 0 0 0 0), upper := (rows 67 50 7 201 209 225 64 128), lower := (rows 67 50 7 8 16 32 64 128), losses := [{ target := 1, region := (rows 1 0 4 13 21 37 255 255), good := (rows 249 240 253 200 208 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 135 178 135 136 144 160 128 128) }] }

theorem profile15_node41 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,3] 6 193 profile15_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,3] 6 193 profile15_node41_cert).mp (by decide +kernel))

def profile15_node42_cert : CutBound 8 := { lost := (rows 0 64 2 64 0 0 0 0), upper := (rows 67 50 69 139 147 163 64 128), lower := (rows 67 50 69 8 16 32 64 128), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 255 255), good := (rows 197 240 197 200 208 224 192 192) },{ target := 6, region := (rows 1 7 4 13 21 37 0 255), good := (rows 187 178 191 136 144 160 128 128) }] }

theorem profile15_node42 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,65] 6 131 profile15_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,65] 6 131 profile15_node42_cert).mp (by decide +kernel))

def profile15_node43_cert : CutBound 8 := { lost := (rows 0 0 1 2 0 0 0 0), upper := (rows 67 50 70 137 145 161 64 128), lower := (rows 67 50 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 255 255), good := (rows 198 246 198 200 208 224 192 192) },{ target := 1, region := (rows 1 0 4 9 17 33 255 255), good := (rows 249 240 196 200 208 224 192 192) }] }

theorem profile15_node43 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,66] 6 129 profile15_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,66] 6 129 profile15_node43_cert).mp (by decide +kernel))

def profile15_node44_cert : CutBound 8 := { lost := (rows 0 0 66 0 0 0 0 0), upper := (rows 67 50 133 203 211 227 64 128), lower := (rows 67 50 133 8 16 32 64 128), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 255 255), good := (rows 197 240 197 200 208 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 135 178 133 136 144 160 128 128) }] }

theorem profile15_node44 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,129] 6 195 profile15_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,129] 6 195 profile15_node44_cert).mp (by decide +kernel))

def profile15_node45_cert : CutBound 8 := { lost := (rows 0 0 1 2 0 0 0 0), upper := (rows 67 50 134 201 209 225 64 128), lower := (rows 67 50 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 255 255), good := (rows 198 246 198 200 208 224 192 192) },{ target := 1, region := (rows 1 0 4 9 17 33 255 255), good := (rows 249 240 196 200 208 224 192 192) }] }

theorem profile15_node45 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,130] 6 193 profile15_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,130] 6 193 profile15_node45_cert).mp (by decide +kernel))

def profile15_node46_cert : CutBound 8 := { lost := (rows 0 0 3 0 0 0 0 0), upper := (rows 67 50 196 139 147 163 64 128), lower := (rows 67 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 198 246 196 204 212 228 196 196) },{ target := 1, region := (rows 1 0 255 8 16 32 255 255), good := (rows 197 244 196 204 212 228 196 196) }] }

theorem profile15_node46 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,192] 6 131 profile15_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48,192] 6 131 profile15_node46_cert).mp (by decide +kernel))

def profile15_node40_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile15_node40_route : Route 8 := (fun mask => (mask,id))

theorem profile15_node40 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,48] 6 (by decide) (choices 2) [3,65,66,129,130,192] profile15_node40_route profile15_node40_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile15_node41
  · exact profile15_node42
  · exact profile15_node43
  · exact profile15_node44
  · exact profile15_node45
  · exact profile15_node46

def profile15_node47_cert : CutBound 8 := { lost := (rows 0 0 64 64 0 0 0 0), upper := (rows 67 67 183 187 179 179 64 128), lower := (rows 67 67 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 2 7 11 19 35 0 255), good := (rows 191 191 132 136 144 160 128 128) }] }

theorem profile15_node47 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,65] 6 179 profile15_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,65] 6 179 profile15_node47_cert).mp (by decide +kernel))

def profile15_node48_cert : CutBound 8 := { lost := (rows 0 1 64 64 0 0 0 0), upper := (rows 67 82 167 171 179 163 64 128), lower := (rows 67 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 194 210 196 200 210 224 192 192) },{ target := 6, region := (rows 1 2 5 9 17 33 0 255), good := (rows 191 146 132 136 144 160 128 128) }] }

theorem profile15_node48 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,80] 6 163 profile15_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,80] 6 163 profile15_node48_cert).mp (by decide +kernel))

def profile15_node49_cert : CutBound 8 := { lost := (rows 128 64 0 0 0 0 0 0), upper := (rows 67 131 247 251 243 243 64 128), lower := (rows 67 131 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 131 131 132 136 144 160 128 128) },{ target := 7, region := (rows 3 2 4 8 16 32 255 0), good := (rows 67 67 68 72 80 96 64 64) }] }

theorem profile15_node49 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,129] 6 243 profile15_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,129] 6 243 profile15_node49_cert).mp (by decide +kernel))

def profile15_node50_cert : CutBound 8 := { lost := (rows 0 65 0 0 0 0 0 0), upper := (rows 67 146 231 235 243 227 64 128), lower := (rows 67 146 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 194 210 196 200 210 224 192 192) },{ target := 6, region := (rows 1 18 4 8 16 32 0 255), good := (rows 131 146 132 136 146 160 128 128) }] }

theorem profile15_node50 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,144] 6 227 profile15_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,144] 6 227 profile15_node50_cert).mp (by decide +kernel))

def profile15_node51_cert : CutBound 8 := { lost := (rows 0 1 64 64 0 0 0 0), upper := (rows 67 194 183 187 179 179 64 128), lower := (rows 67 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 194 194 198 202 210 226 194 194) },{ target := 6, region := (rows 1 2 5 9 17 33 0 255), good := (rows 191 130 132 136 144 160 128 128) }] }

theorem profile15_node51 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,192] 6 179 profile15_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66,192] 6 179 profile15_node51_cert).mp (by decide +kernel))

def profile15_node38_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile15_node38_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile15_node38 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [66] 6 (by decide) (choices 2) [17,48,65,80,129,144,192] profile15_node38_route profile15_node38_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile15_node39
  · exact profile15_node40
  · exact profile15_node47
  · exact profile15_node48
  · exact profile15_node49
  · exact profile15_node50
  · exact profile15_node51

def profile15_node52_cert : CutBound 8 := { lost := (rows 130 0 0 0 0 0 0 0), upper := (rows 81 227 231 235 243 227 64 128), lower := (rows 81 2 4 8 16 32 64 128), losses := [{ target := 1, region := (rows 17 0 4 8 16 32 255 255), good := (rows 209 192 196 200 209 224 192 192) },{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 66 68 72 81 96 64 64) }] }

theorem profile15_node52 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [80] 6 227 profile15_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [80] 6 227 profile15_node52_cert).mp (by decide +kernel))

def profile15_node55_cert : CutBound 8 := { lost := (rows 2 0 0 1 0 0 0 0), upper := (rows 193 19 7 234 242 226 64 128), lower := (rows 193 19 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 255 255), good := (rows 192 250 254 200 208 224 192 192) },{ target := 1, region := (rows 255 0 4 8 16 32 255 255), good := (rows 193 209 197 201 209 225 193 193) }] }

theorem profile15_node55 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,3] 6 226 profile15_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,3] 6 226 profile15_node55_cert).mp (by decide +kernel))

def profile15_node56_cert : CutBound 8 := { lost := (rows 2 0 2 1 0 0 0 0), upper := (rows 193 19 37 202 210 226 64 128), lower := (rows 193 19 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 192 250 228 200 208 224 192 192) },{ target := 1, region := (rows 255 0 36 8 16 32 255 255), good := (rows 193 209 229 201 209 229 193 193) }] }

theorem profile15_node56 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,33] 6 194 profile15_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,33] 6 194 profile15_node56_cert).mp (by decide +kernel))

def profile15_node58_cert : CutBound 8 := { lost := (rows 2 0 1 0 0 0 0 0), upper := (rows 193 19 38 11 208 224 64 128), lower := (rows 193 19 38 11 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 14 8 255 255 255 255), good := (rows 240 246 246 254 240 240 240 240) },{ target := 1, region := (rows 255 0 4 8 255 255 255 255), good := (rows 241 241 245 249 241 241 241 241) }] }

theorem profile15_node58 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,3] 6 192 profile15_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,3] 6 192 profile15_node58_cert).mp (by decide +kernel))

def profile15_node59_cert : CutBound 8 := { lost := (rows 2 0 1 2 0 0 0 0), upper := (rows 193 19 38 73 146 162 64 128), lower := (rows 193 19 38 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 255 255), good := (rows 192 246 246 200 208 224 192 192) },{ target := 1, region := (rows 255 0 4 255 16 32 255 255), good := (rows 201 217 237 201 217 233 201 201) }] }

theorem profile15_node59 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,65] 6 130 profile15_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,65] 6 130 profile15_node59_cert).mp (by decide +kernel))

def profile15_node60_cert : CutBound 8 := { lost := (rows 2 0 0 1 0 0 0 0), upper := (rows 193 19 38 74 145 161 64 128), lower := (rows 193 19 38 74 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 14 16 32 255 255), good := (rows 192 218 238 202 208 224 192 192) },{ target := 1, region := (rows 255 0 4 8 255 255 255 255), good := (rows 241 241 245 249 241 241 241 241) }] }

theorem profile15_node60 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,66] 6 129 profile15_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,66] 6 129 profile15_node60_cert).mp (by decide +kernel))

def profile15_node61_cert : CutBound 8 := { lost := (rows 2 0 0 3 0 0 0 0), upper := (rows 193 19 38 200 19 35 64 128), lower := (rows 193 19 38 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 218 238 200 216 232 200 200) },{ target := 1, region := (rows 255 0 4 255 16 32 255 255), good := (rows 201 217 237 201 217 233 201 201) }] }

theorem profile15_node61 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,192] 6 3 profile15_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34,192] 6 3 profile15_node61_cert).mp (by decide +kernel))

def profile15_node57_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile15_node57_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node57 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,34] 6 (by decide) (choices 2) [3,65,66,192] profile15_node57_route profile15_node57_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node58
  · exact profile15_node59
  · exact profile15_node60
  · exact profile15_node61

def profile15_node62_cert : CutBound 8 := { lost := (rows 2 0 2 1 0 0 0 0), upper := (rows 193 19 69 170 178 162 64 128), lower := (rows 193 19 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 192 250 196 200 208 224 192 192) },{ target := 1, region := (rows 255 0 255 8 16 32 255 255), good := (rows 197 213 197 205 213 229 197 197) }] }

theorem profile15_node62 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,65] 6 162 profile15_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,65] 6 162 profile15_node62_cert).mp (by decide +kernel))

def profile15_node63_cert : CutBound 8 := { lost := (rows 2 0 1 0 0 0 0 0), upper := (rows 193 19 70 171 179 163 64 128), lower := (rows 193 19 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 192 214 198 200 208 224 192 192) },{ target := 1, region := (rows 255 0 4 8 16 32 255 255), good := (rows 193 209 197 201 209 225 193 193) }] }

theorem profile15_node63 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,66] 6 163 profile15_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,66] 6 163 profile15_node63_cert).mp (by decide +kernel))

def profile15_node64_cert : CutBound 8 := { lost := (rows 2 0 3 0 0 0 0 0), upper := (rows 193 19 100 139 147 163 64 128), lower := (rows 193 19 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 255 255), good := (rows 192 210 228 200 208 228 192 192) },{ target := 1, region := (rows 255 0 36 8 16 32 255 255), good := (rows 193 209 229 201 209 229 193 193) }] }

theorem profile15_node64 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,96] 6 131 profile15_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,96] 6 131 profile15_node64_cert).mp (by decide +kernel))

def profile15_node65_cert : CutBound 8 := { lost := (rows 2 0 3 0 0 0 0 0), upper := (rows 193 19 196 43 51 35 64 128), lower := (rows 193 19 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 214 196 204 212 228 196 196) },{ target := 1, region := (rows 255 0 255 8 16 32 255 255), good := (rows 197 213 197 205 213 229 197 197) }] }

theorem profile15_node65 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,192] 6 35 profile15_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17,192] 6 35 profile15_node65_cert).mp (by decide +kernel))

def profile15_node54_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile15_node54_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node54 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,17] 6 (by decide) (choices 2) [3,33,34,65,66,96,192] profile15_node54_route profile15_node54_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile15_node55
  · exact profile15_node56
  · exact profile15_node57
  · exact profile15_node62
  · exact profile15_node63
  · exact profile15_node64
  · exact profile15_node65

def profile15_node68_cert : CutBound 8 := { lost := (rows 2 1 0 0 0 0 0 0), upper := (rows 193 50 7 11 208 224 64 128), lower := (rows 193 50 7 11 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 1, region := (rows 255 0 4 8 255 255 255 255), good := (rows 241 241 245 249 241 241 241 241) }] }

theorem profile15_node68 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,3] 6 192 profile15_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,3] 6 192 profile15_node68_cert).mp (by decide +kernel))

def profile15_node69_cert : CutBound 8 := { lost := (rows 2 1 0 2 0 0 0 0), upper := (rows 193 50 7 73 146 162 64 128), lower := (rows 193 50 7 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 1, region := (rows 255 0 4 255 16 32 255 255), good := (rows 201 249 205 201 217 233 201 201) }] }

theorem profile15_node69 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,65] 6 130 profile15_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,65] 6 130 profile15_node69_cert).mp (by decide +kernel))

def profile15_node70_cert : CutBound 8 := { lost := (rows 2 0 0 1 0 0 0 0), upper := (rows 193 50 7 74 145 161 64 128), lower := (rows 193 50 7 74 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 14 16 32 255 255), good := (rows 192 250 206 202 208 224 192 192) },{ target := 1, region := (rows 255 0 4 8 255 255 255 255), good := (rows 241 241 245 249 241 241 241 241) }] }

theorem profile15_node70 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,66] 6 129 profile15_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,66] 6 129 profile15_node70_cert).mp (by decide +kernel))

def profile15_node71_cert : CutBound 8 := { lost := (rows 2 0 0 3 0 0 0 0), upper := (rows 193 50 7 200 19 35 64 128), lower := (rows 193 50 7 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 250 206 200 216 232 200 200) },{ target := 1, region := (rows 255 0 4 255 16 32 255 255), good := (rows 201 249 205 201 217 233 201 201) }] }

theorem profile15_node71 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,192] 6 3 profile15_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3,192] 6 3 profile15_node71_cert).mp (by decide +kernel))

def profile15_node67_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile15_node67_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node67 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,3] 6 (by decide) (choices 2) [3,65,66,192] profile15_node67_route profile15_node67_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node68
  · exact profile15_node69
  · exact profile15_node70
  · exact profile15_node71

def profile15_node72_cert : CutBound 8 := { lost := (rows 2 0 2 0 0 0 0 0), upper := (rows 193 50 69 139 147 163 64 128), lower := (rows 193 50 69 8 16 32 64 128), losses := [{ target := 1, region := (rows 255 0 255 8 16 32 255 255), good := (rows 197 245 197 205 213 229 197 197) }] }

theorem profile15_node72 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,65] 6 131 profile15_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,65] 6 131 profile15_node72_cert).mp (by decide +kernel))

def profile15_node73_cert : CutBound 8 := { lost := (rows 2 0 1 0 0 0 0 0), upper := (rows 193 50 70 139 147 163 64 128), lower := (rows 193 50 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 192 246 198 200 208 224 192 192) },{ target := 1, region := (rows 255 0 4 8 16 32 255 255), good := (rows 193 241 197 201 209 225 193 193) }] }

theorem profile15_node73 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,66] 6 131 profile15_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,66] 6 131 profile15_node73_cert).mp (by decide +kernel))

def profile15_node74_cert : CutBound 8 := { lost := (rows 2 0 3 0 0 0 0 0), upper := (rows 193 50 196 11 19 35 64 128), lower := (rows 193 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 246 196 204 212 228 196 196) },{ target := 1, region := (rows 255 0 255 8 16 32 255 255), good := (rows 197 245 197 205 213 229 197 197) }] }

theorem profile15_node74 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,192] 6 3 profile15_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48,192] 6 3 profile15_node74_cert).mp (by decide +kernel))

def profile15_node66_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile15_node66_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node66 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,48] 6 (by decide) (choices 2) [3,65,66,192] profile15_node66_route profile15_node66_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node67
  · exact profile15_node72
  · exact profile15_node73
  · exact profile15_node74

def profile15_node75_cert : CutBound 8 := { lost := (rows 2 0 64 64 0 0 0 0), upper := (rows 193 67 183 187 179 179 64 128), lower := (rows 193 67 4 8 16 32 64 128), losses := [{ target := 1, region := (rows 255 0 4 8 16 32 255 255), good := (rows 193 193 197 201 209 225 193 193) },{ target := 6, region := (rows 1 2 6 10 18 34 0 255), good := (rows 129 191 132 136 144 160 128 128) }] }

theorem profile15_node75 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,65] 6 179 profile15_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,65] 6 179 profile15_node75_cert).mp (by decide +kernel))

def profile15_node76_cert : CutBound 8 := { lost := (rows 2 1 0 0 0 0 0 0), upper := (rows 193 82 167 171 179 163 64 128), lower := (rows 193 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 192 210 196 200 210 224 192 192) },{ target := 1, region := (rows 255 0 4 8 16 32 255 255), good := (rows 193 209 197 201 209 225 193 193) }] }

theorem profile15_node76 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,80] 6 163 profile15_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,80] 6 163 profile15_node76_cert).mp (by decide +kernel))

def profile15_node77_cert : CutBound 8 := { lost := (rows 2 1 0 0 0 0 0 0), upper := (rows 193 194 55 59 51 51 64 128), lower := (rows 193 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 194 194 198 202 210 226 194 194) },{ target := 1, region := (rows 255 0 4 8 16 32 255 255), good := (rows 193 193 197 201 209 225 193 193) }] }

theorem profile15_node77 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,192] 6 51 profile15_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192,192] 6 51 profile15_node77_cert).mp (by decide +kernel))

def profile15_node53_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile15_node53_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node53 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [192] 6 (by decide) (choices 2) [17,48,65,80,192] profile15_node53_route profile15_node53_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile15_node54
  · exact profile15_node66
  · exact profile15_node75
  · exact profile15_node76
  · exact profile15_node77

def profile15_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile15_node0_route : Route 8 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile15_node0 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [] 6 (by decide) (choices 2) [18,48,66,80,192] profile15_node0_route profile15_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile15_node1
  · exact profile15_node21
  · exact profile15_node38
  · exact profile15_node52
  · exact profile15_node53

theorem profile15 : Upper (D (n:=8) [34,34,32,32,17,17,2,2]) (R (n:=8) [34,34,32,32,17,17,2,2]) [] 6 := profile15_node0


#print axioms profile15
end Delivery.SmallBudgetTenFinite8
