import SmallBudgetTenFinite8Profile019Part000

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile19_node120_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node120_route : Route 8 := (fun mask => (mask,id))

theorem profile19_node120 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,17] 6 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] profile19_node120_route profile19_node120_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node121
  · exact profile19_node122
  · exact profile19_node123
  · exact profile19_node124
  · exact profile19_node125
  · exact profile19_node126
  · exact profile19_node127
  · exact profile19_node128
  · exact profile19_node129
  · exact profile19_node130

def profile19_node131_cert : CutBound 8 := { lost := (rows 16 16 64 64 0 0 0 0), upper := (rows 97 67 151 155 147 179 64 128), lower := (rows 97 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 255 255), good := (rows 227 195 196 200 192 227 192 192) },{ target := 6, region := (rows 1 2 6 10 18 34 0 255), good := (rows 161 191 132 136 144 160 128 128) }] }

theorem profile19_node131 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,65] 6 147 profile19_node131_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,65] 6 147 profile19_node131_cert).mp (by decide +kernel))

def profile19_node132_cert : CutBound 8 := { lost := (rows 144 129 0 0 0 0 0 0), upper := (rows 97 82 151 155 147 179 64 128), lower := (rows 97 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 224 210 196 200 210 224 192 192) },{ target := 4, region := (rows 33 2 4 8 0 32 255 255), good := (rows 225 194 196 200 192 225 192 192) },{ target := 7, region := (rows 33 18 4 8 16 32 255 0), good := (rows 97 82 68 72 82 97 64 64) }] }

theorem profile19_node132 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,80] 6 147 profile19_node132_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,80] 6 147 profile19_node132_cert).mp (by decide +kernel))

def profile19_node133_cert : CutBound 8 := { lost := (rows 16 80 0 0 0 0 0 0), upper := (rows 97 131 215 219 211 243 64 128), lower := (rows 97 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 255 255), good := (rows 227 195 196 200 192 227 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 163 131 132 136 144 160 128 128) }] }

theorem profile19_node133 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,129] 6 211 profile19_node133_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,129] 6 211 profile19_node133_cert).mp (by decide +kernel))

def profile19_node134_cert : CutBound 8 := { lost := (rows 16 65 0 0 0 0 0 0), upper := (rows 97 146 215 219 211 243 64 128), lower := (rows 97 146 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 224 210 196 200 210 224 192 192) },{ target := 4, region := (rows 33 2 4 8 0 32 255 255), good := (rows 225 194 196 200 192 225 192 192) },{ target := 6, region := (rows 1 18 4 8 16 32 0 255), good := (rows 161 146 132 136 146 160 128 128) }] }

theorem profile19_node134 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,144] 6 211 profile19_node134_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,144] 6 211 profile19_node134_cert).mp (by decide +kernel))

def profile19_node135_cert : CutBound 8 := { lost := (rows 16 17 0 0 0 0 0 0), upper := (rows 97 194 151 155 147 179 64 128), lower := (rows 97 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 226 194 198 202 210 226 194 194) },{ target := 4, region := (rows 33 255 4 8 0 32 255 255), good := (rows 227 194 198 202 194 227 194 194) }] }

theorem profile19_node135 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,192] 6 147 profile19_node135_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96,192] 6 147 profile19_node135_cert).mp (by decide +kernel))

def profile19_node119_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node119_route : Route 8 := (fun mask => (mask,id))

theorem profile19_node119 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [96] 6 (by decide) (choices 2) [17,65,80,129,144,192] profile19_node119_route profile19_node119_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node120
  · exact profile19_node131
  · exact profile19_node132
  · exact profile19_node133
  · exact profile19_node134
  · exact profile19_node135

def profile19_node138_cert : CutBound 8 := { lost := (rows 16 0 16 1 0 0 0 0), upper := (rows 193 19 7 248 240 240 64 128), lower := (rows 193 19 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 254 248 248 248 248 248) },{ target := 4, region := (rows 255 2 6 8 0 32 255 255), good := (rows 193 199 199 201 193 225 193 193) }] }

theorem profile19_node138 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,3] 6 240 profile19_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,3] 6 240 profile19_node138_cert).mp (by decide +kernel))

def profile19_node139_cert : CutBound 8 := { lost := (rows 16 0 0 17 0 0 0 0), upper := (rows 193 19 21 234 242 226 64 128), lower := (rows 193 19 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 192 250 212 200 208 224 192 192) },{ target := 4, region := (rows 255 2 4 10 0 34 255 255), good := (rows 193 235 197 201 193 225 193 193) }] }

theorem profile19_node139 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,17] 6 226 profile19_node139_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,17] 6 226 profile19_node139_cert).mp (by decide +kernel))

def profile19_node140_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 193 19 22 233 241 225 64 128), lower := (rows 193 19 22 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 192 214 214 200 208 224 192 192) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 239 233 233 233 233 233) }] }

theorem profile19_node140 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,18] 6 225 profile19_node140_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,18] 6 225 profile19_node140_cert).mp (by decide +kernel))

def profile19_node141_cert : CutBound 8 := { lost := (rows 16 0 16 1 0 0 0 0), upper := (rows 193 19 37 218 210 242 64 128), lower := (rows 193 19 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 192 250 228 200 208 224 192 192) },{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 195 229 201 193 229 193 193) }] }

theorem profile19_node141 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,33] 6 210 profile19_node141_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,33] 6 210 profile19_node141_cert).mp (by decide +kernel))

def profile19_node143_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 19 38 25 208 224 64 128), lower := (rows 193 19 38 25 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 255 255 255 255), good := (rows 240 246 246 248 240 240 240 240) },{ target := 4, region := (rows 255 2 6 8 0 255 255 255), good := (rows 225 231 231 233 225 225 225 225) }] }

theorem profile19_node143 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,17] 6 192 profile19_node143_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,17] 6 192 profile19_node143_cert).mp (by decide +kernel))

def profile19_node144_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 193 19 38 73 144 176 64 128), lower := (rows 193 19 38 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 255 255 255 255), good := (rows 240 246 246 248 240 240 240 240) },{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 203 239 201 201 233 201 201) }] }

theorem profile19_node144 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,65] 6 144 profile19_node144_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,65] 6 144 profile19_node144_cert).mp (by decide +kernel))

def profile19_node145_cert : CutBound 8 := { lost := (rows 16 0 16 1 0 0 0 0), upper := (rows 193 19 38 88 145 161 64 128), lower := (rows 193 19 38 88 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 26 16 32 255 255), good := (rows 192 218 238 216 216 224 192 192) },{ target := 4, region := (rows 255 2 6 8 0 255 255 255), good := (rows 225 231 231 233 225 225 225 225) }] }

theorem profile19_node145 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,80] 6 129 profile19_node145_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,80] 6 129 profile19_node145_cert).mp (by decide +kernel))

def profile19_node146_cert : CutBound 8 := { lost := (rows 16 0 0 17 0 0 0 0), upper := (rows 193 19 38 200 17 49 64 128), lower := (rows 193 19 38 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 218 238 200 216 232 200 200) },{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 203 239 201 201 233 201 201) }] }

theorem profile19_node146 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,192] 6 17 profile19_node146_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34,192] 6 17 profile19_node146_cert).mp (by decide +kernel))

def profile19_node142_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node142_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node142 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,34] 6 (by decide) (choices 2) [17,65,80,192] profile19_node142_route profile19_node142_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node143
  · exact profile19_node144
  · exact profile19_node145
  · exact profile19_node146

def profile19_node148_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 193 19 52 11 208 224 64 128), lower := (rows 193 19 52 11 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 255 255 255 255), good := (rows 244 246 244 254 244 244 244 244) },{ target := 4, region := (rows 255 2 4 10 0 255 255 255), good := (rows 225 235 229 235 225 225 225 225) }] }

theorem profile19_node148 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,3] 6 192 profile19_node148_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,3] 6 192 profile19_node148_cert).mp (by decide +kernel))

def profile19_node149_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 193 19 52 73 146 162 64 128), lower := (rows 193 19 52 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 18 34 255 255), good := (rows 192 246 244 200 208 224 192 192) },{ target := 4, region := (rows 255 2 4 255 0 34 255 255), good := (rows 201 235 237 201 201 233 201 201) }] }

theorem profile19_node149 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,65] 6 130 profile19_node149_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,65] 6 130 profile19_node149_cert).mp (by decide +kernel))

def profile19_node150_cert : CutBound 8 := { lost := (rows 16 0 0 17 0 0 0 0), upper := (rows 193 19 52 74 145 161 64 128), lower := (rows 193 19 52 74 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 255 255), good := (rows 192 218 244 202 208 224 192 192) },{ target := 4, region := (rows 255 2 4 10 0 255 255 255), good := (rows 225 235 229 235 225 225 225 225) }] }

theorem profile19_node150 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,66] 6 129 profile19_node150_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,66] 6 129 profile19_node150_cert).mp (by decide +kernel))

def profile19_node151_cert : CutBound 8 := { lost := (rows 16 0 0 17 0 0 0 0), upper := (rows 193 19 52 200 19 35 64 128), lower := (rows 193 19 52 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 218 252 200 216 232 200 200) },{ target := 4, region := (rows 255 2 4 255 0 34 255 255), good := (rows 201 235 237 201 201 233 201 201) }] }

theorem profile19_node151 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,192] 6 3 profile19_node151_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48,192] 6 3 profile19_node151_cert).mp (by decide +kernel))

def profile19_node147_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node147_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node147 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,48] 6 (by decide) (choices 2) [3,65,66,192] profile19_node147_route profile19_node147_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node148
  · exact profile19_node149
  · exact profile19_node150
  · exact profile19_node151

def profile19_node152_cert : CutBound 8 := { lost := (rows 16 0 16 1 0 0 0 0), upper := (rows 193 19 69 186 178 178 64 128), lower := (rows 193 19 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 192 250 196 200 208 224 192 192) },{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) }] }

theorem profile19_node152 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,65] 6 178 profile19_node152_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,65] 6 178 profile19_node152_cert).mp (by decide +kernel))

def profile19_node153_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 19 70 185 177 177 64 128), lower := (rows 193 19 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 192 214 198 200 208 224 192 192) },{ target := 4, region := (rows 255 2 6 8 0 32 255 255), good := (rows 193 199 199 201 193 225 193 193) }] }

theorem profile19_node153 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,66] 6 177 profile19_node153_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,66] 6 177 profile19_node153_cert).mp (by decide +kernel))

def profile19_node154_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 193 19 84 171 179 163 64 128), lower := (rows 193 19 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 192 214 212 200 212 224 192 192) },{ target := 4, region := (rows 255 2 4 10 0 34 255 255), good := (rows 193 235 197 201 193 225 193 193) }] }

theorem profile19_node154 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,80] 6 163 profile19_node154_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,80] 6 163 profile19_node154_cert).mp (by decide +kernel))

def profile19_node155_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 19 100 155 147 179 64 128), lower := (rows 193 19 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 255 255), good := (rows 192 210 228 200 208 228 192 192) },{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 195 229 201 193 229 193 193) }] }

theorem profile19_node155 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,96] 6 147 profile19_node155_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,96] 6 147 profile19_node155_cert).mp (by decide +kernel))

def profile19_node156_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 19 196 59 51 51 64 128), lower := (rows 193 19 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 214 196 204 212 228 196 196) },{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) }] }

theorem profile19_node156 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,192] 6 51 profile19_node156_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17,192] 6 51 profile19_node156_cert).mp (by decide +kernel))

def profile19_node137_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile19_node137_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node137 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,17] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] profile19_node137_route profile19_node137_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node138
  · exact profile19_node139
  · exact profile19_node140
  · exact profile19_node141
  · exact profile19_node142
  · exact profile19_node147
  · exact profile19_node152
  · exact profile19_node153
  · exact profile19_node154
  · exact profile19_node155
  · exact profile19_node156

def profile19_node158_cert : CutBound 8 := { lost := (rows 16 16 16 1 0 0 0 0), upper := (rows 193 35 7 216 208 240 64 128), lower := (rows 193 35 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 254 248 248 248 248 248) },{ target := 4, region := (rows 255 34 38 8 0 32 255 255), good := (rows 193 231 199 201 193 231 193 193) }] }

theorem profile19_node158 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,3] 6 208 profile19_node158_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,3] 6 208 profile19_node158_cert).mp (by decide +kernel))

def profile19_node159_cert : CutBound 8 := { lost := (rows 16 16 0 1 0 0 0 0), upper := (rows 193 35 21 218 210 242 64 128), lower := (rows 193 35 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 192 250 212 200 208 224 192 192) },{ target := 4, region := (rows 255 34 4 8 0 32 255 255), good := (rows 193 227 197 201 193 227 193 193) }] }

theorem profile19_node159 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,17] 6 210 profile19_node159_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,17] 6 210 profile19_node159_cert).mp (by decide +kernel))

def profile19_node161_cert : CutBound 8 := { lost := (rows 16 16 1 0 0 0 0 0), upper := (rows 193 35 22 25 208 224 64 128), lower := (rows 193 35 22 25 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 255 255 255 255), good := (rows 240 246 246 248 240 240 240 240) },{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) }] }

theorem profile19_node161 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,17] 6 192 profile19_node161_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,17] 6 192 profile19_node161_cert).mp (by decide +kernel))

def profile19_node162_cert : CutBound 8 := { lost := (rows 16 16 1 16 0 0 0 0), upper := (rows 193 35 22 73 144 176 64 128), lower := (rows 193 35 22 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 255 255 255 255), good := (rows 240 246 246 248 240 240 240 240) },{ target := 4, region := (rows 255 34 4 255 0 32 255 255), good := (rows 201 235 207 201 201 235 201 201) }] }

theorem profile19_node162 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,65] 6 144 profile19_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,65] 6 144 profile19_node162_cert).mp (by decide +kernel))

def profile19_node163_cert : CutBound 8 := { lost := (rows 16 16 0 1 0 0 0 0), upper := (rows 193 35 22 88 145 161 64 128), lower := (rows 193 35 22 88 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 28 16 32 255 255), good := (rows 192 226 222 216 216 224 192 192) },{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) }] }

theorem profile19_node163 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,80] 6 129 profile19_node163_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,80] 6 129 profile19_node163_cert).mp (by decide +kernel))

def profile19_node164_cert : CutBound 8 := { lost := (rows 16 16 0 17 0 0 0 0), upper := (rows 193 35 22 200 17 49 64 128), lower := (rows 193 35 22 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 234 222 200 216 232 200 200) },{ target := 4, region := (rows 255 34 4 255 0 32 255 255), good := (rows 201 235 207 201 201 235 201 201) }] }

theorem profile19_node164 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,192] 6 17 profile19_node164_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18,192] 6 17 profile19_node164_cert).mp (by decide +kernel))

def profile19_node160_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node160_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node160 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,18] 6 (by decide) (choices 2) [17,65,80,192] profile19_node160_route profile19_node160_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node161
  · exact profile19_node162
  · exact profile19_node163
  · exact profile19_node164

def profile19_node165_cert : CutBound 8 := { lost := (rows 16 16 16 1 0 0 0 0), upper := (rows 193 35 69 154 146 178 64 128), lower := (rows 193 35 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 192 250 196 200 208 224 192 192) },{ target := 4, region := (rows 255 34 255 8 0 32 255 255), good := (rows 197 231 197 205 197 231 197 197) }] }

theorem profile19_node165 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,65] 6 146 profile19_node165_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,65] 6 146 profile19_node165_cert).mp (by decide +kernel))

def profile19_node166_cert : CutBound 8 := { lost := (rows 16 16 17 0 0 0 0 0), upper := (rows 193 35 70 153 145 177 64 128), lower := (rows 193 35 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 192 230 198 200 208 224 192 192) },{ target := 4, region := (rows 255 34 38 8 0 32 255 255), good := (rows 193 231 199 201 193 231 193 193) }] }

theorem profile19_node166 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,66] 6 145 profile19_node166_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,66] 6 145 profile19_node166_cert).mp (by decide +kernel))

def profile19_node167_cert : CutBound 8 := { lost := (rows 16 16 1 0 0 0 0 0), upper := (rows 193 35 84 155 147 179 64 128), lower := (rows 193 35 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 255 255), good := (rows 192 226 212 200 212 224 192 192) },{ target := 4, region := (rows 255 34 4 8 0 32 255 255), good := (rows 193 227 197 201 193 227 193 193) }] }

theorem profile19_node167 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,80] 6 147 profile19_node167_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,80] 6 147 profile19_node167_cert).mp (by decide +kernel))

def profile19_node168_cert : CutBound 8 := { lost := (rows 16 16 17 0 0 0 0 0), upper := (rows 193 35 196 27 19 51 64 128), lower := (rows 193 35 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 230 196 204 212 228 196 196) },{ target := 4, region := (rows 255 34 255 8 0 32 255 255), good := (rows 197 231 197 205 197 231 197 197) }] }

theorem profile19_node168 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,192] 6 19 profile19_node168_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33,192] 6 19 profile19_node168_cert).mp (by decide +kernel))

def profile19_node157_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node157_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node157 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,33] 6 (by decide) (choices 2) [3,17,18,65,66,80,192] profile19_node157_route profile19_node157_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node158
  · exact profile19_node159
  · exact profile19_node160
  · exact profile19_node165
  · exact profile19_node166
  · exact profile19_node167
  · exact profile19_node168

def profile19_node171_cert : CutBound 8 := { lost := (rows 16 1 16 0 0 0 0 0), upper := (rows 193 50 7 25 208 224 64 128), lower := (rows 193 50 7 25 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 4, region := (rows 255 2 6 8 0 255 255 255), good := (rows 225 231 231 233 225 225 225 225) }] }

theorem profile19_node171 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,17] 6 192 profile19_node171_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,17] 6 192 profile19_node171_cert).mp (by decide +kernel))

def profile19_node172_cert : CutBound 8 := { lost := (rows 16 1 16 16 0 0 0 0), upper := (rows 193 50 7 73 144 176 64 128), lower := (rows 193 50 7 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 4, region := (rows 255 2 6 255 0 32 255 255), good := (rows 201 239 207 201 201 233 201 201) }] }

theorem profile19_node172 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,65] 6 144 profile19_node172_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,65] 6 144 profile19_node172_cert).mp (by decide +kernel))

def profile19_node173_cert : CutBound 8 := { lost := (rows 16 0 16 1 0 0 0 0), upper := (rows 193 50 7 88 145 161 64 128), lower := (rows 193 50 7 88 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 26 16 32 255 255), good := (rows 192 250 206 216 216 224 192 192) },{ target := 4, region := (rows 255 2 6 8 0 255 255 255), good := (rows 225 231 231 233 225 225 225 225) }] }

theorem profile19_node173 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,80] 6 129 profile19_node173_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,80] 6 129 profile19_node173_cert).mp (by decide +kernel))

def profile19_node174_cert : CutBound 8 := { lost := (rows 16 0 16 17 0 0 0 0), upper := (rows 193 50 7 200 17 49 64 128), lower := (rows 193 50 7 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 250 206 200 216 232 200 200) },{ target := 4, region := (rows 255 2 6 255 0 32 255 255), good := (rows 201 239 207 201 201 233 201 201) }] }

theorem profile19_node174 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,192] 6 17 profile19_node174_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3,192] 6 17 profile19_node174_cert).mp (by decide +kernel))

def profile19_node170_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node170_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node170 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,3] 6 (by decide) (choices 2) [17,65,80,192] profile19_node170_route profile19_node170_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node171
  · exact profile19_node172
  · exact profile19_node173
  · exact profile19_node174

def profile19_node176_cert : CutBound 8 := { lost := (rows 16 1 0 16 0 0 0 0), upper := (rows 193 50 21 11 208 224 64 128), lower := (rows 193 50 21 11 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 4, region := (rows 255 2 4 10 0 255 255 255), good := (rows 225 235 229 235 225 225 225 225) }] }

theorem profile19_node176 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,3] 6 192 profile19_node176_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,3] 6 192 profile19_node176_cert).mp (by decide +kernel))

def profile19_node177_cert : CutBound 8 := { lost := (rows 16 1 0 16 0 0 0 0), upper := (rows 193 50 21 73 146 162 64 128), lower := (rows 193 50 21 73 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 250 242 242 242 242) },{ target := 4, region := (rows 255 2 4 255 0 34 255 255), good := (rows 201 235 205 201 201 233 201 201) }] }

theorem profile19_node177 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,65] 6 130 profile19_node177_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,65] 6 130 profile19_node177_cert).mp (by decide +kernel))

def profile19_node178_cert : CutBound 8 := { lost := (rows 16 0 0 17 0 0 0 0), upper := (rows 193 50 21 74 145 161 64 128), lower := (rows 193 50 21 74 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 255 255), good := (rows 192 250 212 202 208 224 192 192) },{ target := 4, region := (rows 255 2 4 10 0 255 255 255), good := (rows 225 235 229 235 225 225 225 225) }] }

theorem profile19_node178 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,66] 6 129 profile19_node178_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,66] 6 129 profile19_node178_cert).mp (by decide +kernel))

def profile19_node179_cert : CutBound 8 := { lost := (rows 16 0 0 17 0 0 0 0), upper := (rows 193 50 21 200 19 35 64 128), lower := (rows 193 50 21 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 250 220 200 216 232 200 200) },{ target := 4, region := (rows 255 2 4 255 0 34 255 255), good := (rows 201 235 205 201 201 233 201 201) }] }

theorem profile19_node179 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,192] 6 3 profile19_node179_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17,192] 6 3 profile19_node179_cert).mp (by decide +kernel))

def profile19_node175_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node175_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node175 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,17] 6 (by decide) (choices 2) [3,65,66,192] profile19_node175_route profile19_node175_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node176
  · exact profile19_node177
  · exact profile19_node178
  · exact profile19_node179

def profile19_node180_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 193 50 22 201 209 225 64 128), lower := (rows 193 50 22 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 192 246 214 200 208 224 192 192) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 239 233 233 233 233 233) }] }

theorem profile19_node180 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,18] 6 193 profile19_node180_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,18] 6 193 profile19_node180_cert).mp (by decide +kernel))

def profile19_node181_cert : CutBound 8 := { lost := (rows 16 64 16 64 0 0 0 0), upper := (rows 193 50 69 155 147 179 64 128), lower := (rows 193 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) },{ target := 6, region := (rows 1 7 4 13 21 37 0 255), good := (rows 187 178 191 136 144 160 128 128) }] }

theorem profile19_node181 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,65] 6 147 profile19_node181_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,65] 6 147 profile19_node181_cert).mp (by decide +kernel))

def profile19_node182_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 50 70 153 145 177 64 128), lower := (rows 193 50 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 192 246 198 200 208 224 192 192) },{ target := 4, region := (rows 255 2 6 8 0 32 255 255), good := (rows 193 231 199 201 193 225 193 193) }] }

theorem profile19_node182 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,66] 6 145 profile19_node182_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,66] 6 145 profile19_node182_cert).mp (by decide +kernel))

def profile19_node183_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 193 50 84 139 147 163 64 128), lower := (rows 193 50 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 192 246 212 200 212 224 192 192) },{ target := 4, region := (rows 255 2 4 10 0 34 255 255), good := (rows 193 235 197 201 193 225 193 193) }] }

theorem profile19_node183 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,80] 6 131 profile19_node183_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,80] 6 131 profile19_node183_cert).mp (by decide +kernel))

def profile19_node184_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 50 196 27 19 51 64 128), lower := (rows 193 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 246 196 204 212 228 196 196) },{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) }] }

theorem profile19_node184 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,192] 6 19 profile19_node184_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48,192] 6 19 profile19_node184_cert).mp (by decide +kernel))

def profile19_node169_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile19_node169_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node169 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,48] 6 (by decide) (choices 2) [3,17,18,65,66,80,192] profile19_node169_route profile19_node169_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node170
  · exact profile19_node175
  · exact profile19_node180
  · exact profile19_node181
  · exact profile19_node182
  · exact profile19_node183
  · exact profile19_node184

def profile19_node185_cert : CutBound 8 := { lost := (rows 16 16 64 64 0 0 0 0), upper := (rows 193 67 183 187 179 179 64 128), lower := (rows 193 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 6, region := (rows 1 2 6 10 18 34 0 255), good := (rows 129 191 132 136 144 160 128 128) }] }

theorem profile19_node185 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,65] 6 179 profile19_node185_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,65] 6 179 profile19_node185_cert).mp (by decide +kernel))

def profile19_node186_cert : CutBound 8 := { lost := (rows 16 129 0 0 0 0 0 0), upper := (rows 193 82 183 187 179 179 64 128), lower := (rows 193 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 192 210 196 200 210 224 192 192) },{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) },{ target := 7, region := (rows 1 18 4 8 16 32 255 0), good := (rows 65 82 68 72 82 96 64 64) }] }

theorem profile19_node186 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,80] 6 179 profile19_node186_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,80] 6 179 profile19_node186_cert).mp (by decide +kernel))

def profile19_node187_cert : CutBound 8 := { lost := (rows 16 17 0 0 0 0 0 0), upper := (rows 193 98 151 155 147 179 64 128), lower := (rows 193 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 192 226 196 200 208 226 192 192) },{ target := 4, region := (rows 255 34 4 8 0 32 255 255), good := (rows 193 227 197 201 193 227 193 193) }] }

theorem profile19_node187 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,96] 6 147 profile19_node187_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,96] 6 147 profile19_node187_cert).mp (by decide +kernel))

def profile19_node188_cert : CutBound 8 := { lost := (rows 16 17 0 0 0 0 0 0), upper := (rows 193 194 55 59 51 51 64 128), lower := (rows 193 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 194 194 198 202 210 226 194 194) },{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) }] }

theorem profile19_node188 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,192] 6 51 profile19_node188_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192,192] 6 51 profile19_node188_cert).mp (by decide +kernel))

def profile19_node136_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile19_node136_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node136 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [192] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile19_node136_route profile19_node136_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node137
  · exact profile19_node157
  · exact profile19_node169
  · exact profile19_node185
  · exact profile19_node186
  · exact profile19_node187
  · exact profile19_node188

def profile19_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile19_node0_route : Route 8 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile19_node0 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [] 6 (by decide) (choices 2) [18,34,48,66,80,96,192] profile19_node0_route profile19_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node1
  · exact profile19_node28
  · exact profile19_node47
  · exact profile19_node75
  · exact profile19_node92
  · exact profile19_node119
  · exact profile19_node136

theorem profile19 : Upper (D (n:=8) [34,33,32,32,18,17,2,2]) (R (n:=8) [34,33,32,32,18,17,2,2]) [] 6 := profile19_node0


#print axioms profile19
end Delivery.SmallBudgetTenFinite8
