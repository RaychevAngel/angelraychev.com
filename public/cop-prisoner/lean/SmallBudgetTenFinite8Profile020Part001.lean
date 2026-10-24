import SmallBudgetTenFinite8Profile020Part000

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile20_node131_cert : CutBound 8 := { lost := (rows 0 128 144 0 0 0 0 0), upper := (rows 49 82 69 142 150 166 64 128), lower := (rows 49 82 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 229 194 197 200 192 224 192 192) },{ target := 7, region := (rows 1 19 5 8 16 32 255 0), good := (rows 119 82 71 72 82 96 64 64) }] }

theorem profile20_node131 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,65] 6 134 profile20_node131_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,65] 6 134 profile20_node131_cert).mp (by decide +kernel))

def profile20_node132_cert : CutBound 8 := { lost := (rows 64 0 16 64 0 0 0 0), upper := (rows 49 82 70 141 149 165 64 128), lower := (rows 49 82 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 225 198 198 200 192 224 192 192) },{ target := 6, region := (rows 5 2 4 12 20 36 0 255), good := (rows 177 146 191 136 144 160 128 128) }] }

theorem profile20_node132 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,66] 6 133 profile20_node132_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,66] 6 133 profile20_node132_cert).mp (by decide +kernel))

def profile20_node133_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 49 82 133 206 214 230 64 128), lower := (rows 49 82 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 229 194 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 181 146 133 136 144 160 128 128) }] }

theorem profile20_node133 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,129] 6 198 profile20_node133_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,129] 6 198 profile20_node133_cert).mp (by decide +kernel))

def profile20_node134_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 49 82 134 205 213 229 64 128), lower := (rows 49 82 134 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 225 198 198 200 192 224 192 192) },{ target := 6, region := (rows 1 2 6 8 16 32 0 255), good := (rows 177 150 134 136 144 160 128 128) }] }

theorem profile20_node134 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,130] 6 197 profile20_node134_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,130] 6 197 profile20_node134_cert).mp (by decide +kernel))

def profile20_node135_cert : Bound 8 := { allowed := (rows 192 128 0 208 0 0 0 0), upper := (rows 49 82 196 143 151 167 64 128), lower := (rows 49 82 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 229 198 196 204 196 228 196 196) }] }

theorem profile20_node135 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,192] 6 135 profile20_node135_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80,192] 6 135 profile20_node135_cert).mp (by decide +kernel))

def profile20_node129_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node129_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node129 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,80] 6 (by decide) (choices 2) [3,65,66,129,130,192] profile20_node129_route profile20_node129_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node130
  · exact profile20_node131
  · exact profile20_node132
  · exact profile20_node133
  · exact profile20_node134
  · exact profile20_node135

def profile20_node137_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 49 194 7 220 212 244 64 128), lower := (rows 49 194 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 231 194 199 202 194 226 194 194) }] }

theorem profile20_node137 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,3] 6 212 profile20_node137_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,3] 6 212 profile20_node137_cert).mp (by decide +kernel))

def profile20_node138_cert : CutBound 8 := { lost := (rows 0 16 0 16 0 0 0 0), upper := (rows 49 194 21 206 214 230 64 128), lower := (rows 49 194 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 12 0 36 255 255), good := (rows 227 194 239 202 194 226 194 194) }] }

theorem profile20_node138 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,17] 6 198 profile20_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,17] 6 198 profile20_node138_cert).mp (by decide +kernel))

def profile20_node141_cert : CutBound 8 := { lost := (rows 64 16 0 64 0 0 0 0), upper := (rows 49 194 22 13 80 160 64 128), lower := (rows 49 194 22 13 80 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 255 255 255), good := (rows 227 226 230 239 226 226 226 226) },{ target := 6, region := (rows 21 2 4 12 16 255 0 255), good := (rows 177 162 191 173 177 160 160 160) }] }

theorem profile20_node141 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,5,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,5,64] 6 128 profile20_node141_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,5,64] 6 128 profile20_node141_cert).mp (by decide +kernel))

def profile20_node140_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile20_node140_route : Route 8 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node140 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,5] 6 (by decide) (choices 1) [64] profile20_node140_route profile20_node140_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node141

def profile20_node142_cert : CutBound 8 := { lost := (rows 0 16 0 16 0 0 0 0), upper := (rows 49 194 22 73 148 164 64 128), lower := (rows 49 194 22 73 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 9 0 36 255 255), good := (rows 235 194 230 203 194 226 194 194) }] }

theorem profile20_node142 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,65] 6 132 profile20_node142_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,65] 6 132 profile20_node142_cert).mp (by decide +kernel))

def profile20_node143_cert : CutBound 8 := { lost := (rows 0 16 0 16 0 0 0 0), upper := (rows 49 194 22 76 145 161 64 128), lower := (rows 49 194 22 76 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 12 0 33 255 255), good := (rows 227 194 206 206 194 226 194 194) }] }

theorem profile20_node143 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,68] 6 129 profile20_node143_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,68] 6 129 profile20_node143_cert).mp (by decide +kernel))

def profile20_node144_cert : Bound 8 := { allowed := (rows 192 16 192 16 0 0 0 0), upper := (rows 49 194 22 200 21 37 64 128), lower := (rows 49 194 22 200 16 32 64 128), losses := [] }

theorem profile20_node144 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,192] 6 5 profile20_node144_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18,192] 6 5 profile20_node144_cert).mp (by decide +kernel))

def profile20_node139_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node139_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node139 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,18] 6 (by decide) (choices 2) [5,65,68,192] profile20_node139_route profile20_node139_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node140
  · exact profile20_node142
  · exact profile20_node143
  · exact profile20_node144

def profile20_node145_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 49 194 69 158 150 182 64 128), lower := (rows 49 194 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 32 255 255), good := (rows 231 194 199 202 194 226 194 194) }] }

theorem profile20_node145 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,65] 6 150 profile20_node145_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,65] 6 150 profile20_node145_cert).mp (by decide +kernel))

def profile20_node146_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 49 194 70 157 149 181 64 128), lower := (rows 49 194 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 255 8 0 32 255 255), good := (rows 231 198 198 206 198 230 198 198) }] }

theorem profile20_node146 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,66] 6 149 profile20_node146_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,66] 6 149 profile20_node146_cert).mp (by decide +kernel))

def profile20_node147_cert : Bound 8 := { allowed := (rows 192 0 128 208 0 0 0 0), upper := (rows 49 194 84 143 151 167 64 128), lower := (rows 49 194 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 227 194 198 202 194 226 194 194) }] }

theorem profile20_node147 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,80] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,80] 6 135 profile20_node147_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,80] 6 135 profile20_node147_cert).mp (by decide +kernel))

def profile20_node148_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 49 194 196 31 23 55 64 128), lower := (rows 49 194 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 255 8 0 32 255 255), good := (rows 231 198 198 206 198 230 198 198) }] }

theorem profile20_node148 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,192] 6 23 profile20_node148_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192,192] 6 23 profile20_node148_cert).mp (by decide +kernel))

def profile20_node136_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node136_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node136 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48,192] 6 (by decide) (choices 2) [3,17,18,65,66,80,192] profile20_node136_route profile20_node136_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node137
  · exact profile20_node138
  · exact profile20_node139
  · exact profile20_node145
  · exact profile20_node146
  · exact profile20_node147
  · exact profile20_node148

def profile20_node110_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 12 => 3 | 36 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node110_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node110 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [48] 6 (by decide) (choices 2) [5,17,20,65,68,80,192] profile20_node110_route profile20_node110_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node111
  · exact profile20_node116
  · exact profile20_node117
  · exact profile20_node127
  · exact profile20_node128
  · exact profile20_node129
  · exact profile20_node136

def profile20_node149_cert : CutBound 8 := { lost := (rows 144 0 0 0 0 0 0 0), upper := (rows 67 247 245 253 245 245 64 128), lower := (rows 67 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 7, region := (rows 3 2 4 8 16 32 255 0), good := (rows 67 67 68 72 80 96 64 64) }] }

theorem profile20_node149 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [66] 6 245 profile20_node149_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [66] 6 245 profile20_node149_cert).mp (by decide +kernel))

def profile20_node152_cert : CutBound 8 := { lost := (rows 0 64 64 16 0 0 0 0), upper := (rows 81 7 22 232 240 224 64 128), lower := (rows 81 7 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 233 239 238 232 232 232 232 232) },{ target := 6, region := (rows 1 3 5 8 16 32 0 255), good := (rows 151 135 150 136 144 160 128 128) }] }

theorem profile20_node152 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,18] 6 224 profile20_node152_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,18] 6 224 profile20_node152_cert).mp (by decide +kernel))

def profile20_node154_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 81 7 38 88 144 160 64 128), lower := (rows 81 7 38 88 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 7 8 0 255 255 255), good := (rows 231 231 230 232 224 224 224 224) }] }

theorem profile20_node154 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,34,80] 6 128 profile20_node154_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,34,80] 6 128 profile20_node154_cert).mp (by decide +kernel))

def profile20_node155_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 81 7 38 152 208 224 64 128), lower := (rows 81 7 38 152 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 7 8 0 255 255 255), good := (rows 231 231 230 232 224 224 224 224) }] }

theorem profile20_node155 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,34,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,34,144] 6 192 profile20_node155_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,34,144] 6 192 profile20_node155_cert).mp (by decide +kernel))

def profile20_node156_cert : CutBound 8 := { lost := (rows 0 64 64 16 0 0 0 0), upper := (rows 81 7 38 200 144 176 64 128), lower := (rows 81 7 38 200 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 32 255 255), good := (rows 201 207 238 200 200 232 200 200) },{ target := 6, region := (rows 1 3 7 8 255 255 0 255), good := (rows 183 183 182 184 176 176 176 176) }] }

theorem profile20_node156 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,34,192] 6 144 profile20_node156_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,34,192] 6 144 profile20_node156_cert).mp (by decide +kernel))

def profile20_node153_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node153_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node153 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,34] 6 (by decide) (choices 2) [80,144,192] profile20_node153_route profile20_node153_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile20_node154
  · exact profile20_node155
  · exact profile20_node156

def profile20_node157_cert : CutBound 8 := { lost := (rows 128 128 0 16 0 0 0 0), upper := (rows 81 7 52 202 210 226 64 128), lower := (rows 81 7 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 255 255), good := (rows 193 239 228 200 192 224 192 192) },{ target := 7, region := (rows 21 6 4 8 16 32 255 0), good := (rows 81 71 119 72 81 96 64 64) }] }

theorem profile20_node157 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,48] 6 194 profile20_node157_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,48] 6 194 profile20_node157_cert).mp (by decide +kernel))

def profile20_node158_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 81 7 70 184 176 176 64 128), lower := (rows 81 7 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 7 8 0 32 255 255), good := (rows 199 199 198 200 192 224 192 192) }] }

theorem profile20_node158 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,66] 6 176 profile20_node158_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,66] 6 176 profile20_node158_cert).mp (by decide +kernel))

def profile20_node159_cert : CutBound 8 := { lost := (rows 0 0 0 80 0 0 0 0), upper := (rows 81 7 84 170 178 162 64 128), lower := (rows 81 7 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 255 255), good := (rows 193 239 196 200 192 224 192 192) },{ target := 6, region := (rows 1 2 4 10 18 34 0 255), good := (rows 145 191 148 136 144 160 128 128) }] }

theorem profile20_node159 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,80] 6 162 profile20_node159_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,80] 6 162 profile20_node159_cert).mp (by decide +kernel))

def profile20_node160_cert : CutBound 8 := { lost := (rows 0 0 16 64 0 0 0 0), upper := (rows 81 7 100 154 146 178 64 128), lower := (rows 81 7 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 255 255), good := (rows 193 199 228 200 192 228 192 192) },{ target := 6, region := (rows 1 2 4 10 18 34 0 255), good := (rows 145 191 164 136 144 160 128 128) }] }

theorem profile20_node160 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,96] 6 146 profile20_node160_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,96] 6 146 profile20_node160_cert).mp (by decide +kernel))

def profile20_node161_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 81 7 134 248 240 240 64 128), lower := (rows 81 7 134 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 7 8 0 32 255 255), good := (rows 199 199 198 200 192 224 192 192) }] }

theorem profile20_node161 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,130] 6 240 profile20_node161_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,130] 6 240 profile20_node161_cert).mp (by decide +kernel))

def profile20_node162_cert : CutBound 8 := { lost := (rows 0 64 64 16 0 0 0 0), upper := (rows 81 7 148 234 242 226 64 128), lower := (rows 81 7 148 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 255 255), good := (rows 193 239 196 200 192 224 192 192) },{ target := 6, region := (rows 1 3 21 8 16 32 0 255), good := (rows 151 135 148 136 148 160 128 128) }] }

theorem profile20_node162 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,144] 6 226 profile20_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,144] 6 226 profile20_node162_cert).mp (by decide +kernel))

def profile20_node163_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 81 7 164 218 210 242 64 128), lower := (rows 81 7 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 255 255), good := (rows 193 199 228 200 192 228 192 192) },{ target := 6, region := (rows 1 2 36 8 16 32 0 255), good := (rows 145 135 164 136 144 164 128 128) }] }

theorem profile20_node163 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,160] 6 210 profile20_node163_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,160] 6 210 profile20_node163_cert).mp (by decide +kernel))

def profile20_node164_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 81 7 196 186 178 178 64 128), lower := (rows 81 7 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 255 8 0 32 255 255), good := (rows 199 199 196 204 196 228 196 196) }] }

theorem profile20_node164 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,192] 6 178 profile20_node164_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5,192] 6 178 profile20_node164_cert).mp (by decide +kernel))

def profile20_node151_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node151_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node151 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,5] 6 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192] profile20_node151_route profile20_node151_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node152
  · exact profile20_node153
  · exact profile20_node157
  · exact profile20_node158
  · exact profile20_node159
  · exact profile20_node160
  · exact profile20_node161
  · exact profile20_node162
  · exact profile20_node163
  · exact profile20_node164

def profile20_node165_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 81 19 230 238 246 230 64 128), lower := (rows 81 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 255 255), good := (rows 193 239 196 200 192 224 192 192) }] }

theorem profile20_node165 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,17] 6 230 profile20_node165_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,17] 6 230 profile20_node165_cert).mp (by decide +kernel))

def profile20_node167_cert : CutBound 8 := { lost := (rows 0 64 64 16 0 0 0 0), upper := (rows 81 22 7 232 240 224 64 128), lower := (rows 81 22 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 255 255 255), good := (rows 233 238 239 232 232 232 232 232) },{ target := 6, region := (rows 1 3 5 8 16 32 0 255), good := (rows 151 150 135 136 144 160 128 128) }] }

theorem profile20_node167 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,3] 6 224 profile20_node167_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,3] 6 224 profile20_node167_cert).mp (by decide +kernel))

def profile20_node168_cert : CutBound 8 := { lost := (rows 128 0 0 16 0 0 0 0), upper := (rows 81 22 37 202 210 226 64 128), lower := (rows 81 22 37 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 255 255), good := (rows 193 238 229 200 192 224 192 192) },{ target := 7, region := (rows 19 2 4 8 16 32 255 0), good := (rows 81 87 101 72 81 96 64 64) }] }

theorem profile20_node168 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,33] 6 194 profile20_node168_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,33] 6 194 profile20_node168_cert).mp (by decide +kernel))

def profile20_node169_cert : CutBound 8 := { lost := (rows 128 0 0 16 0 0 0 0), upper := (rows 81 22 38 201 209 225 64 128), lower := (rows 81 22 38 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 233 198 230 200 192 224 192 192) },{ target := 7, region := (rows 19 2 4 8 16 32 255 0), good := (rows 81 87 103 72 81 96 64 64) }] }

theorem profile20_node169 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,34] 6 193 profile20_node169_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,34] 6 193 profile20_node169_cert).mp (by decide +kernel))

def profile20_node170_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 81 22 69 170 178 162 64 128), lower := (rows 81 22 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 255 255), good := (rows 197 238 197 200 192 224 192 192) }] }

theorem profile20_node170 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,65] 6 162 profile20_node170_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,65] 6 162 profile20_node170_cert).mp (by decide +kernel))

def profile20_node171_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 81 22 70 169 177 161 64 128), lower := (rows 81 22 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 198 198 200 192 224 192 192) }] }

theorem profile20_node171 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,66] 6 161 profile20_node171_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,66] 6 161 profile20_node171_cert).mp (by decide +kernel))

def profile20_node172_cert : CutBound 8 := { lost := (rows 128 0 144 0 0 0 0 0), upper := (rows 81 22 100 139 147 163 64 128), lower := (rows 81 22 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 255 255), good := (rows 193 198 228 200 192 228 192 192) },{ target := 7, region := (rows 19 2 36 8 16 32 255 0), good := (rows 81 87 100 72 81 100 64 64) }] }

theorem profile20_node172 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,96] 6 131 profile20_node172_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,96] 6 131 profile20_node172_cert).mp (by decide +kernel))

def profile20_node173_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 81 22 133 234 242 226 64 128), lower := (rows 81 22 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 255 255), good := (rows 197 238 197 200 192 224 192 192) }] }

theorem profile20_node173 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,129] 6 226 profile20_node173_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,129] 6 226 profile20_node173_cert).mp (by decide +kernel))

def profile20_node174_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 81 22 134 233 241 225 64 128), lower := (rows 81 22 134 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 9 0 33 255 255), good := (rows 233 198 198 200 192 224 192 192) }] }

theorem profile20_node174 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,130] 6 225 profile20_node174_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,130] 6 225 profile20_node174_cert).mp (by decide +kernel))

def profile20_node175_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 81 22 164 203 211 227 64 128), lower := (rows 81 22 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 255 255), good := (rows 193 198 228 200 192 228 192 192) },{ target := 6, region := (rows 1 2 36 8 16 32 0 255), good := (rows 145 150 164 136 144 164 128 128) }] }

theorem profile20_node175 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,160] 6 195 profile20_node175_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,160] 6 195 profile20_node175_cert).mp (by decide +kernel))

def profile20_node176_cert : Bound 8 := { allowed := (rows 128 192 0 208 0 0 0 0), upper := (rows 81 22 196 171 179 163 64 128), lower := (rows 81 22 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 198 196 204 196 228 196 196) }] }

theorem profile20_node176 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,192] 6 163 profile20_node176_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20,192] 6 163 profile20_node176_cert).mp (by decide +kernel))

def profile20_node166_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile20_node166_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node166 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,20] 6 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] profile20_node166_route profile20_node166_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node167
  · exact profile20_node168
  · exact profile20_node169
  · exact profile20_node170
  · exact profile20_node171
  · exact profile20_node172
  · exact profile20_node173
  · exact profile20_node174
  · exact profile20_node175
  · exact profile20_node176

def profile20_node178_cert : CutBound 8 := { lost := (rows 128 0 0 16 0 0 0 0), upper := (rows 81 35 22 204 212 228 64 128), lower := (rows 81 35 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 255 255), good := (rows 193 227 238 200 192 224 192 192) },{ target := 7, region := (rows 21 2 4 8 16 32 255 0), good := (rows 81 99 87 72 81 96 64 64) }] }

theorem profile20_node178 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,18] 6 196 profile20_node178_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,18] 6 196 profile20_node178_cert).mp (by decide +kernel))

def profile20_node179_cert : CutBound 8 := { lost := (rows 0 0 16 64 0 0 0 0), upper := (rows 81 35 70 156 148 180 64 128), lower := (rows 81 35 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 193 231 198 200 192 224 192 192) },{ target := 6, region := (rows 1 2 4 12 20 36 0 255), good := (rows 145 163 190 136 144 160 128 128) }] }

theorem profile20_node179 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,66] 6 148 profile20_node179_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,66] 6 148 profile20_node179_cert).mp (by decide +kernel))

def profile20_node180_cert : CutBound 8 := { lost := (rows 128 0 128 0 0 0 0 0), upper := (rows 81 35 84 142 150 166 64 128), lower := (rows 81 35 84 8 16 32 64 128), losses := [{ target := 7, region := (rows 21 2 21 8 16 32 255 0), good := (rows 85 103 85 72 85 96 64 64) }] }

theorem profile20_node180 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,80] 6 134 profile20_node180_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,80] 6 134 profile20_node180_cert).mp (by decide +kernel))

def profile20_node181_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 81 35 134 220 212 244 64 128), lower := (rows 81 35 134 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 193 231 198 200 192 224 192 192) },{ target := 6, region := (rows 1 2 6 8 16 32 0 255), good := (rows 145 167 134 136 144 160 128 128) }] }

theorem profile20_node181 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,130] 6 212 profile20_node181_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,130] 6 212 profile20_node181_cert).mp (by decide +kernel))

def profile20_node182_cert : CutBound 8 := { lost := (rows 128 0 64 0 0 0 0 0), upper := (rows 81 35 148 206 214 230 64 128), lower := (rows 81 35 148 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 2 21 8 16 32 0 255), good := (rows 149 167 148 136 148 160 128 128) },{ target := 7, region := (rows 21 2 4 8 16 32 255 0), good := (rows 81 99 85 72 81 96 64 64) }] }

theorem profile20_node182 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,144] 6 198 profile20_node182_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,144] 6 198 profile20_node182_cert).mp (by decide +kernel))

def profile20_node183_cert : CutBound 8 := { lost := (rows 128 0 16 0 0 0 0 0), upper := (rows 81 35 196 158 150 182 64 128), lower := (rows 81 35 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 231 196 204 196 228 196 196) },{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 99 68 72 81 96 64 64) }] }

theorem profile20_node183 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,192] 6 150 profile20_node183_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33,192] 6 150 profile20_node183_cert).mp (by decide +kernel))

def profile20_node177_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node177_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node177 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,33] 6 (by decide) (choices 2) [18,66,80,130,144,192] profile20_node177_route profile20_node177_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node178
  · exact profile20_node179
  · exact profile20_node180
  · exact profile20_node181
  · exact profile20_node182
  · exact profile20_node183

def profile20_node186_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 81 38 7 88 144 160 64 128), lower := (rows 81 38 7 88 16 32 64 128), losses := [{ target := 4, region := (rows 1 7 5 8 0 255 255 255), good := (rows 231 230 231 232 224 224 224 224) }] }

theorem profile20_node186 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,3,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,3,80] 6 128 profile20_node186_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,3,80] 6 128 profile20_node186_cert).mp (by decide +kernel))

def profile20_node187_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 81 38 7 152 208 224 64 128), lower := (rows 81 38 7 152 16 32 64 128), losses := [{ target := 4, region := (rows 1 7 5 8 0 255 255 255), good := (rows 231 230 231 232 224 224 224 224) }] }

theorem profile20_node187 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,3,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,3,144] 6 192 profile20_node187_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,3,144] 6 192 profile20_node187_cert).mp (by decide +kernel))

def profile20_node188_cert : CutBound 8 := { lost := (rows 0 64 64 16 0 0 0 0), upper := (rows 81 38 7 200 144 176 64 128), lower := (rows 81 38 7 200 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 255 0 32 255 255), good := (rows 201 238 207 200 200 232 200 200) },{ target := 6, region := (rows 1 7 5 8 255 255 0 255), good := (rows 183 182 183 184 176 176 176 176) }] }

theorem profile20_node188 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,3,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,3,192] 6 144 profile20_node188_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,3,192] 6 144 profile20_node188_cert).mp (by decide +kernel))

def profile20_node185_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node185_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node185 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,3] 6 (by decide) (choices 2) [80,144,192] profile20_node185_route profile20_node185_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile20_node186
  · exact profile20_node187
  · exact profile20_node188

def profile20_node189_cert : CutBound 8 := { lost := (rows 0 16 0 16 0 0 0 0), upper := (rows 81 38 21 202 210 226 64 128), lower := (rows 81 38 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 6 4 14 0 38 255 255), good := (rows 193 238 239 200 192 224 192 192) }] }

theorem profile20_node189 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,17] 6 194 profile20_node189_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,17] 6 194 profile20_node189_cert).mp (by decide +kernel))

def profile20_node190_cert : CutBound 8 := { lost := (rows 128 0 0 16 0 0 0 0), upper := (rows 81 38 22 201 209 225 64 128), lower := (rows 81 38 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 255 255), good := (rows 233 230 198 200 192 224 192 192) },{ target := 7, region := (rows 21 2 4 8 16 32 255 0), good := (rows 81 103 87 72 81 96 64 64) }] }

theorem profile20_node190 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,18] 6 193 profile20_node190_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,18] 6 193 profile20_node190_cert).mp (by decide +kernel))

def profile20_node191_cert : CutBound 8 := { lost := (rows 0 64 16 64 0 0 0 0), upper := (rows 81 38 69 154 146 178 64 128), lower := (rows 81 38 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 197 230 197 200 192 224 192 192) },{ target := 6, region := (rows 1 6 4 14 22 38 0 255), good := (rows 145 190 191 136 144 160 128 128) }] }

theorem profile20_node191 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,65] 6 146 profile20_node191_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,65] 6 146 profile20_node191_cert).mp (by decide +kernel))

def profile20_node192_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 81 38 70 153 145 177 64 128), lower := (rows 81 38 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 38 8 0 32 255 255), good := (rows 193 230 198 200 192 230 192 192) }] }

theorem profile20_node192 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,66] 6 145 profile20_node192_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,66] 6 145 profile20_node192_cert).mp (by decide +kernel))

def profile20_node193_cert : CutBound 8 := { lost := (rows 128 0 128 0 0 0 0 0), upper := (rows 81 38 84 139 147 163 64 128), lower := (rows 81 38 84 8 16 32 64 128), losses := [{ target := 7, region := (rows 21 2 21 8 16 32 255 0), good := (rows 85 103 85 72 85 96 64 64) }] }

theorem profile20_node193 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,80] 6 131 profile20_node193_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,80] 6 131 profile20_node193_cert).mp (by decide +kernel))

def profile20_node194_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 81 38 133 218 210 242 64 128), lower := (rows 81 38 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 197 230 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 149 166 133 136 144 160 128 128) }] }

theorem profile20_node194 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,129] 6 210 profile20_node194_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,129] 6 210 profile20_node194_cert).mp (by decide +kernel))

def profile20_node195_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 81 38 134 217 209 241 64 128), lower := (rows 81 38 134 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 38 8 0 32 255 255), good := (rows 193 230 198 200 192 230 192 192) }] }

theorem profile20_node195 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,130] 6 209 profile20_node195_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,130] 6 209 profile20_node195_cert).mp (by decide +kernel))

def profile20_node196_cert : CutBound 8 := { lost := (rows 128 0 64 0 0 0 0 0), upper := (rows 81 38 148 203 211 227 64 128), lower := (rows 81 38 148 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 2 21 8 16 32 0 255), good := (rows 149 166 148 136 148 160 128 128) },{ target := 7, region := (rows 21 2 4 8 16 32 255 0), good := (rows 81 103 85 72 81 96 64 64) }] }

theorem profile20_node196 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,144] 6 195 profile20_node196_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,144] 6 195 profile20_node196_cert).mp (by decide +kernel))

def profile20_node197_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 81 38 196 155 147 179 64 128), lower := (rows 81 38 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 255 8 0 32 255 255), good := (rows 197 230 196 204 196 230 196 196) }] }

theorem profile20_node197 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,192] 6 147 profile20_node197_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36,192] 6 147 profile20_node197_cert).mp (by decide +kernel))

def profile20_node184_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node184_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node184 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,36] 6 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] profile20_node184_route profile20_node184_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node185
  · exact profile20_node189
  · exact profile20_node190
  · exact profile20_node191
  · exact profile20_node192
  · exact profile20_node193
  · exact profile20_node194
  · exact profile20_node195
  · exact profile20_node196
  · exact profile20_node197

def profile20_node199_cert : CutBound 8 := { lost := (rows 128 0 128 16 0 0 0 0), upper := (rows 81 50 7 204 212 228 64 128), lower := (rows 81 50 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 255 255), good := (rows 193 226 239 200 192 224 192 192) },{ target := 7, region := (rows 19 2 6 8 16 32 255 0), good := (rows 81 119 71 72 81 96 64 64) }] }

theorem profile20_node199 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,3] 6 196 profile20_node199_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,3] 6 196 profile20_node199_cert).mp (by decide +kernel))

def profile20_node200_cert : CutBound 8 := { lost := (rows 0 64 16 64 0 0 0 0), upper := (rows 81 50 69 142 150 166 64 128), lower := (rows 81 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 197 226 197 200 192 224 192 192) },{ target := 6, region := (rows 1 6 4 12 20 36 0 255), good := (rows 145 178 191 136 144 160 128 128) }] }

theorem profile20_node200 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,65] 6 134 profile20_node200_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,65] 6 134 profile20_node200_cert).mp (by decide +kernel))

def profile20_node201_cert : CutBound 8 := { lost := (rows 128 0 144 0 0 0 0 0), upper := (rows 81 50 70 141 149 165 64 128), lower := (rows 81 50 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 193 230 198 200 192 224 192 192) },{ target := 7, region := (rows 19 2 6 8 16 32 255 0), good := (rows 81 119 71 72 81 96 64 64) }] }

theorem profile20_node201 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,66] 6 133 profile20_node201_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,66] 6 133 profile20_node201_cert).mp (by decide +kernel))

def profile20_node202_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 81 50 133 206 214 230 64 128), lower := (rows 81 50 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 255 255), good := (rows 197 226 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 5 8 16 32 0 255), good := (rows 149 178 133 136 144 160 128 128) }] }

theorem profile20_node202 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,129] 6 198 profile20_node202_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,129] 6 198 profile20_node202_cert).mp (by decide +kernel))

def profile20_node203_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 81 50 134 205 213 229 64 128), lower := (rows 81 50 134 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 255 255), good := (rows 193 230 198 200 192 224 192 192) },{ target := 6, region := (rows 1 2 6 8 16 32 0 255), good := (rows 145 182 134 136 144 160 128 128) }] }

theorem profile20_node203 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,130] 6 197 profile20_node203_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,130] 6 197 profile20_node203_cert).mp (by decide +kernel))

def profile20_node204_cert : Bound 8 := { allowed := (rows 128 192 0 208 0 0 0 0), upper := (rows 81 50 196 143 151 167 64 128), lower := (rows 81 50 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 230 196 204 196 228 196 196) }] }

theorem profile20_node204 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,192] 6 135 profile20_node204_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48,192] 6 135 profile20_node204_cert).mp (by decide +kernel))

def profile20_node198_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node198_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node198 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,48] 6 (by decide) (choices 2) [3,65,66,129,130,192] profile20_node198_route profile20_node198_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node199
  · exact profile20_node200
  · exact profile20_node201
  · exact profile20_node202
  · exact profile20_node203
  · exact profile20_node204

def profile20_node205_cert : CutBound 8 := { lost := (rows 0 16 64 64 0 0 0 0), upper := (rows 81 67 182 190 182 182 64 128), lower := (rows 81 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 6, region := (rows 1 2 6 10 18 34 0 255), good := (rows 145 191 132 136 144 160 128 128) }] }

theorem profile20_node205 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,65] 6 182 profile20_node205_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,65] 6 182 profile20_node205_cert).mp (by decide +kernel))

def profile20_node206_cert : CutBound 8 := { lost := (rows 128 144 0 0 0 0 0 0), upper := (rows 81 70 183 187 179 179 64 128), lower := (rows 81 70 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 255 255), good := (rows 193 198 198 200 192 224 192 192) },{ target := 7, region := (rows 17 6 4 8 16 32 255 0), good := (rows 81 70 70 72 81 96 64 64) }] }

theorem profile20_node206 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,68] 6 179 profile20_node206_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,68] 6 179 profile20_node206_cert).mp (by decide +kernel))

def profile20_node207_cert : CutBound 8 := { lost := (rows 128 128 0 0 0 0 0 0), upper := (rows 81 82 167 175 183 167 64 128), lower := (rows 81 82 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 19 19 4 8 16 32 255 0), good := (rows 83 83 68 72 83 96 64 64) }] }

theorem profile20_node207 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,80] 6 167 profile20_node207_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,80] 6 167 profile20_node207_cert).mp (by decide +kernel))

def profile20_node208_cert : CutBound 8 := { lost := (rows 128 144 0 0 0 0 0 0), upper := (rows 81 98 151 159 151 183 64 128), lower := (rows 81 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) },{ target := 7, region := (rows 17 34 4 8 16 32 255 0), good := (rows 81 98 68 72 81 98 64 64) }] }

theorem profile20_node208 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,96] 6 151 profile20_node208_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,96] 6 151 profile20_node208_cert).mp (by decide +kernel))

def profile20_node209_cert : CutBound 8 := { lost := (rows 0 80 0 0 0 0 0 0), upper := (rows 81 131 246 254 246 246 64 128), lower := (rows 81 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 147 131 132 136 144 160 128 128) }] }

theorem profile20_node209 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,129] 6 246 profile20_node209_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,129] 6 246 profile20_node209_cert).mp (by decide +kernel))

def profile20_node210_cert : CutBound 8 := { lost := (rows 0 80 0 0 0 0 0 0), upper := (rows 81 134 247 251 243 243 64 128), lower := (rows 81 134 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 255 255), good := (rows 193 198 198 200 192 224 192 192) },{ target := 6, region := (rows 1 6 4 8 16 32 0 255), good := (rows 145 134 134 136 144 160 128 128) }] }

theorem profile20_node210 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,132] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,132] 6 243 profile20_node210_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,132] 6 243 profile20_node210_cert).mp (by decide +kernel))

def profile20_node211_cert : CutBound 8 := { lost := (rows 128 64 0 0 0 0 0 0), upper := (rows 81 146 231 239 247 231 64 128), lower := (rows 81 146 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 19 4 8 16 32 0 255), good := (rows 147 146 132 136 146 160 128 128) },{ target := 7, region := (rows 19 2 4 8 16 32 255 0), good := (rows 81 83 68 72 81 96 64 64) }] }

theorem profile20_node211 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,144] 6 231 profile20_node211_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,144] 6 231 profile20_node211_cert).mp (by decide +kernel))

def profile20_node212_cert : CutBound 8 := { lost := (rows 0 80 0 0 0 0 0 0), upper := (rows 81 162 215 223 215 247 64 128), lower := (rows 81 162 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) },{ target := 6, region := (rows 1 34 4 8 16 32 0 255), good := (rows 145 162 132 136 144 162 128 128) }] }

theorem profile20_node212 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,160] 6 215 profile20_node212_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,160] 6 215 profile20_node212_cert).mp (by decide +kernel))

def profile20_node213_cert : CutBound 8 := { lost := (rows 128 16 0 0 0 0 0 0), upper := (rows 81 194 183 191 183 183 64 128), lower := (rows 81 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 195 194 198 202 194 226 194 194) },{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 66 68 72 81 96 64 64) }] }

theorem profile20_node213 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,192] 6 183 profile20_node213_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80,192] 6 183 profile20_node213_cert).mp (by decide +kernel))

def profile20_node150_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node150_route : Route 8 := (fun mask => (mask,id))

theorem profile20_node150 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [80] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] profile20_node150_route profile20_node150_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node151
  · exact profile20_node165
  · exact profile20_node166
  · exact profile20_node177
  · exact profile20_node184
  · exact profile20_node198
  · exact profile20_node205
  · exact profile20_node206
  · exact profile20_node207
  · exact profile20_node208
  · exact profile20_node209
  · exact profile20_node210
  · exact profile20_node211
  · exact profile20_node212
  · exact profile20_node213

def profile20_node214_cert : CutBound 8 := { lost := (rows 144 0 0 0 0 0 0 0), upper := (rows 97 215 215 223 215 247 64 128), lower := (rows 97 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 255 255), good := (rows 225 194 196 200 192 225 192 192) },{ target := 7, region := (rows 33 2 4 8 16 32 255 0), good := (rows 97 66 68 72 80 97 64 64) }] }

theorem profile20_node214 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [96] 6 215 profile20_node214_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [96] 6 215 profile20_node214_cert).mp (by decide +kernel))

def profile20_node216_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 7 246 250 242 242 64 128), lower := (rows 193 7 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 6 4 8 0 32 255 255), good := (rows 193 199 199 201 193 225 193 193) }] }

theorem profile20_node216 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,5] 6 242 profile20_node216_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,5] 6 242 profile20_node216_cert).mp (by decide +kernel))

def profile20_node218_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 19 22 236 244 228 64 128), lower := (rows 193 19 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 12 0 36 255 255), good := (rows 193 195 239 201 193 225 193 193) }] }

theorem profile20_node218 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,18] 6 228 profile20_node218_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,18] 6 228 profile20_node218_cert).mp (by decide +kernel))

def profile20_node220_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 19 38 28 208 224 64 128), lower := (rows 193 19 38 28 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 255 255 255), good := (rows 225 231 231 237 225 225 225 225) }] }

theorem profile20_node220 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,20] 6 192 profile20_node220_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,20] 6 192 profile20_node220_cert).mp (by decide +kernel))

def profile20_node221_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 19 38 76 144 176 64 128), lower := (rows 193 19 38 76 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 12 0 32 255 255), good := (rows 193 195 239 205 193 225 193 193) }] }

theorem profile20_node221 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,68] 6 144 profile20_node221_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,68] 6 144 profile20_node221_cert).mp (by decide +kernel))

def profile20_node222_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 19 38 88 148 164 64 128), lower := (rows 193 19 38 88 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 38 255 255), good := (rows 193 231 231 201 193 225 193 193) }] }

theorem profile20_node222 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,80] 6 132 profile20_node222_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,80] 6 132 profile20_node222_cert).mp (by decide +kernel))

def profile20_node223_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 19 38 200 20 52 64 128), lower := (rows 193 19 38 200 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 203 239 201 201 233 201 201) }] }

theorem profile20_node223 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,192] 6 20 profile20_node223_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34,192] 6 20 profile20_node223_cert).mp (by decide +kernel))

def profile20_node219_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node219_route : Route 8 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node219 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,34] 6 (by decide) (choices 2) [20,68,80,192] profile20_node219_route profile20_node219_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node220
  · exact profile20_node221
  · exact profile20_node222
  · exact profile20_node223

def profile20_node226_cert : CutBound 8 := { lost := (rows 16 0 64 64 0 0 0 0), upper := (rows 193 19 52 14 80 160 64 128), lower := (rows 193 19 52 14 80 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 255 255 255), good := (rows 225 227 229 239 225 225 225 225) },{ target := 6, region := (rows 1 2 22 10 16 255 0 255), good := (rows 161 191 180 174 180 160 160 160) }] }

theorem profile20_node226 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,6,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,6,64] 6 128 profile20_node226_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,6,64] 6 128 profile20_node226_cert).mp (by decide +kernel))

def profile20_node225_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile20_node225_route : Route 8 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node225 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,6] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,6] 6 (by decide) (choices 1) [64] profile20_node225_route profile20_node225_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node226

def profile20_node227_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 19 52 74 148 164 64 128), lower := (rows 193 19 52 74 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 36 255 255), good := (rows 193 203 229 203 193 225 193 193) }] }

theorem profile20_node227 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,66] 6 132 profile20_node227_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,66] 6 132 profile20_node227_cert).mp (by decide +kernel))

def profile20_node228_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 19 52 76 146 162 64 128), lower := (rows 193 19 52 76 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 12 0 34 255 255), good := (rows 193 227 237 205 193 225 193 193) }] }

theorem profile20_node228 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,68] 6 130 profile20_node228_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,68] 6 130 profile20_node228_cert).mp (by decide +kernel))

def profile20_node229_cert : Bound 8 := { allowed := (rows 16 192 192 16 0 0 0 0), upper := (rows 193 19 52 200 22 38 64 128), lower := (rows 193 19 52 200 16 32 64 128), losses := [] }

theorem profile20_node229 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,192] 6 6 profile20_node229_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48,192] 6 6 profile20_node229_cert).mp (by decide +kernel))

def profile20_node224_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node224_route : Route 8 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node224 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,48] 6 (by decide) (choices 2) [6,66,68,192] profile20_node224_route profile20_node224_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node225
  · exact profile20_node227
  · exact profile20_node228
  · exact profile20_node229

def profile20_node230_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 19 70 188 180 180 64 128), lower := (rows 193 19 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 32 255 255), good := (rows 193 199 199 201 193 225 193 193) }] }

theorem profile20_node230 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,66] 6 180 profile20_node230_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,66] 6 180 profile20_node230_cert).mp (by decide +kernel))

def profile20_node231_cert : Bound 8 := { allowed := (rows 0 192 128 208 0 0 0 0), upper := (rows 193 19 84 174 182 166 64 128), lower := (rows 193 19 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) }] }

theorem profile20_node231 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,80] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,80] 6 166 profile20_node231_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,80] 6 166 profile20_node231_cert).mp (by decide +kernel))

def profile20_node232_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 19 100 158 150 182 64 128), lower := (rows 193 19 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 195 229 201 193 229 193 193) }] }

theorem profile20_node232 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,96] 6 150 profile20_node232_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,96] 6 150 profile20_node232_cert).mp (by decide +kernel))

def profile20_node233_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 19 196 62 54 54 64 128), lower := (rows 193 19 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) }] }

theorem profile20_node233 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,192] 6 54 profile20_node233_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17,192] 6 54 profile20_node233_cert).mp (by decide +kernel))

def profile20_node217_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node217_route : Route 8 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node217 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,17] 6 (by decide) (choices 2) [18,34,48,66,80,96,192] profile20_node217_route profile20_node217_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node218
  · exact profile20_node219
  · exact profile20_node224
  · exact profile20_node230
  · exact profile20_node231
  · exact profile20_node232
  · exact profile20_node233

def profile20_node235_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 22 7 248 240 240 64 128), lower := (rows 193 22 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 32 255 255), good := (rows 193 199 199 201 193 225 193 193) }] }

theorem profile20_node235 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,3] 6 240 profile20_node235_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,3] 6 240 profile20_node235_cert).mp (by decide +kernel))

def profile20_node236_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 22 21 234 242 226 64 128), lower := (rows 193 22 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 34 255 255), good := (rows 193 239 197 201 193 225 193 193) }] }

theorem profile20_node236 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,17] 6 226 profile20_node236_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,17] 6 226 profile20_node236_cert).mp (by decide +kernel))

def profile20_node237_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 22 22 233 241 225 64 128), lower := (rows 193 22 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 239 239 233 233 233 233 233) }] }

theorem profile20_node237 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,18] 6 225 profile20_node237_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,18] 6 225 profile20_node237_cert).mp (by decide +kernel))

def profile20_node238_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 22 37 218 210 242 64 128), lower := (rows 193 22 37 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 199 229 201 193 229 193 193) }] }

theorem profile20_node238 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,33] 6 210 profile20_node238_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,33] 6 210 profile20_node238_cert).mp (by decide +kernel))

def profile20_node240_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 22 38 25 208 224 64 128), lower := (rows 193 22 38 25 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 255 255 255), good := (rows 225 231 231 233 225 225 225 225) }] }

theorem profile20_node240 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,17] 6 192 profile20_node240_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,17] 6 192 profile20_node240_cert).mp (by decide +kernel))

def profile20_node241_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 22 38 73 144 176 64 128), lower := (rows 193 22 38 73 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 207 239 201 201 233 201 201) }] }

theorem profile20_node241 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,65] 6 144 profile20_node241_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,65] 6 144 profile20_node241_cert).mp (by decide +kernel))

def profile20_node242_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 22 38 88 145 161 64 128), lower := (rows 193 22 38 88 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 255 255 255), good := (rows 225 231 231 233 225 225 225 225) }] }

theorem profile20_node242 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,80] 6 129 profile20_node242_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,80] 6 129 profile20_node242_cert).mp (by decide +kernel))

def profile20_node243_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 22 38 200 17 49 64 128), lower := (rows 193 22 38 200 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 207 239 201 201 233 201 201) }] }

theorem profile20_node243 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,192] 6 17 profile20_node243_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34,192] 6 17 profile20_node243_cert).mp (by decide +kernel))

def profile20_node239_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node239_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node239 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,34] 6 (by decide) (choices 2) [17,65,80,192] profile20_node239_route profile20_node239_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node240
  · exact profile20_node241
  · exact profile20_node242
  · exact profile20_node243

def profile20_node244_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 22 52 203 211 227 64 128), lower := (rows 193 22 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 34 255 255), good := (rows 193 239 229 201 193 225 193 193) }] }

theorem profile20_node244 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,48] 6 195 profile20_node244_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,48] 6 195 profile20_node244_cert).mp (by decide +kernel))

def profile20_node245_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 22 69 186 178 178 64 128), lower := (rows 193 22 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) }] }

theorem profile20_node245 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,65] 6 178 profile20_node245_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,65] 6 178 profile20_node245_cert).mp (by decide +kernel))

def profile20_node246_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 22 70 185 177 177 64 128), lower := (rows 193 22 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 32 255 255), good := (rows 193 199 199 201 193 225 193 193) }] }

theorem profile20_node246 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,66] 6 177 profile20_node246_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,66] 6 177 profile20_node246_cert).mp (by decide +kernel))

def profile20_node247_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 22 84 171 179 163 64 128), lower := (rows 193 22 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 34 255 255), good := (rows 193 239 197 201 193 225 193 193) }] }

theorem profile20_node247 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,80] 6 163 profile20_node247_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,80] 6 163 profile20_node247_cert).mp (by decide +kernel))

def profile20_node248_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 22 100 155 147 179 64 128), lower := (rows 193 22 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 199 229 201 193 229 193 193) }] }

theorem profile20_node248 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,96] 6 147 profile20_node248_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,96] 6 147 profile20_node248_cert).mp (by decide +kernel))

def profile20_node249_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 22 196 59 51 51 64 128), lower := (rows 193 22 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) }] }

theorem profile20_node249 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,192] 6 51 profile20_node249_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20,192] 6 51 profile20_node249_cert).mp (by decide +kernel))

def profile20_node234_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node234_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node234 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,20] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] profile20_node234_route profile20_node234_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node235
  · exact profile20_node236
  · exact profile20_node237
  · exact profile20_node238
  · exact profile20_node239
  · exact profile20_node244
  · exact profile20_node245
  · exact profile20_node246
  · exact profile20_node247
  · exact profile20_node248
  · exact profile20_node249

def profile20_node250_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 35 214 222 214 246 64 128), lower := (rows 193 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 34 4 8 0 32 255 255), good := (rows 193 227 197 201 193 227 193 193) }] }

theorem profile20_node250 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,33] 6 214 profile20_node250_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,33] 6 214 profile20_node250_cert).mp (by decide +kernel))

def profile20_node252_cert : CutBound 8 := { lost := (rows 16 16 16 0 0 0 0 0), upper := (rows 193 38 7 216 208 240 64 128), lower := (rows 193 38 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 34 38 8 0 32 255 255), good := (rows 193 231 199 201 193 231 193 193) }] }

theorem profile20_node252 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,3] 6 208 profile20_node252_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,3] 6 208 profile20_node252_cert).mp (by decide +kernel))

def profile20_node254_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 38 21 26 208 224 64 128), lower := (rows 193 38 21 26 16 32 64 128), losses := [{ target := 4, region := (rows 255 6 4 8 0 255 255 255), good := (rows 225 231 231 235 225 225 225 225) }] }

theorem profile20_node254 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,18] 6 192 profile20_node254_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,18] 6 192 profile20_node254_cert).mp (by decide +kernel))

def profile20_node255_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 38 21 74 144 176 64 128), lower := (rows 193 38 21 74 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 32 255 255), good := (rows 193 239 197 203 193 225 193 193) }] }

theorem profile20_node255 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,66] 6 144 profile20_node255_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,66] 6 144 profile20_node255_cert).mp (by decide +kernel))

def profile20_node256_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 38 21 88 146 162 64 128), lower := (rows 193 38 21 88 16 32 64 128), losses := [{ target := 4, region := (rows 255 6 4 8 0 38 255 255), good := (rows 193 231 231 201 193 225 193 193) }] }

theorem profile20_node256 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,80] 6 130 profile20_node256_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,80] 6 130 profile20_node256_cert).mp (by decide +kernel))

def profile20_node257_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 38 21 200 18 50 64 128), lower := (rows 193 38 21 200 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 239 205 201 201 233 201 201) }] }

theorem profile20_node257 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,192] 6 18 profile20_node257_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17,192] 6 18 profile20_node257_cert).mp (by decide +kernel))

def profile20_node253_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node253_route : Route 8 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node253 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,17] 6 (by decide) (choices 2) [18,66,80,192] profile20_node253_route profile20_node253_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node254
  · exact profile20_node255
  · exact profile20_node256
  · exact profile20_node257

def profile20_node259_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 38 22 25 208 224 64 128), lower := (rows 193 38 22 25 16 32 64 128), losses := [{ target := 4, region := (rows 255 6 4 8 0 255 255 255), good := (rows 225 231 231 233 225 225 225 225) }] }

theorem profile20_node259 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,17] 6 192 profile20_node259_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,17] 6 192 profile20_node259_cert).mp (by decide +kernel))


#print axioms profile20_node259
end Delivery.SmallBudgetTenFinite8
