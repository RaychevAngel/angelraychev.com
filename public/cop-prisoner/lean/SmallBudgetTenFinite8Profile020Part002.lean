import SmallBudgetTenFinite8Profile020Part001

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile20_node260_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 38 22 73 144 176 64 128), lower := (rows 193 38 22 73 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 239 207 201 201 233 201 201) }] }

theorem profile20_node260 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,65] 6 144 profile20_node260_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,65] 6 144 profile20_node260_cert).mp (by decide +kernel))

def profile20_node261_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 38 22 88 145 161 64 128), lower := (rows 193 38 22 88 16 32 64 128), losses := [{ target := 4, region := (rows 255 6 4 8 0 255 255 255), good := (rows 225 231 231 233 225 225 225 225) }] }

theorem profile20_node261 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,80] 6 129 profile20_node261_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,80] 6 129 profile20_node261_cert).mp (by decide +kernel))

def profile20_node262_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 38 22 200 17 49 64 128), lower := (rows 193 38 22 200 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 32 255 255), good := (rows 201 239 207 201 201 233 201 201) }] }

theorem profile20_node262 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,192] 6 17 profile20_node262_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18,192] 6 17 profile20_node262_cert).mp (by decide +kernel))

def profile20_node258_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node258_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node258 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,18] 6 (by decide) (choices 2) [17,65,80,192] profile20_node258_route profile20_node258_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node259
  · exact profile20_node260
  · exact profile20_node261
  · exact profile20_node262

def profile20_node263_cert : CutBound 8 := { lost := (rows 16 16 16 0 0 0 0 0), upper := (rows 193 38 69 154 146 178 64 128), lower := (rows 193 38 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 34 255 8 0 32 255 255), good := (rows 197 231 197 205 197 231 197 197) }] }

theorem profile20_node263 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,65] 6 146 profile20_node263_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,65] 6 146 profile20_node263_cert).mp (by decide +kernel))

def profile20_node264_cert : CutBound 8 := { lost := (rows 16 16 16 0 0 0 0 0), upper := (rows 193 38 70 153 145 177 64 128), lower := (rows 193 38 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 34 38 8 0 32 255 255), good := (rows 193 231 199 201 193 231 193 193) }] }

theorem profile20_node264 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,66] 6 145 profile20_node264_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,66] 6 145 profile20_node264_cert).mp (by decide +kernel))

def profile20_node265_cert : CutBound 8 := { lost := (rows 16 0 128 0 0 0 0 0), upper := (rows 193 38 84 155 147 179 64 128), lower := (rows 193 38 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 231 197 201 193 225 193 193) },{ target := 7, region := (rows 1 2 20 8 16 32 255 0), good := (rows 65 102 84 72 84 96 64 64) }] }

theorem profile20_node265 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,80] 6 147 profile20_node265_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,80] 6 147 profile20_node265_cert).mp (by decide +kernel))

def profile20_node266_cert : CutBound 8 := { lost := (rows 16 16 16 0 0 0 0 0), upper := (rows 193 38 196 27 19 51 64 128), lower := (rows 193 38 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 34 255 8 0 32 255 255), good := (rows 197 231 197 205 197 231 197 197) }] }

theorem profile20_node266 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,192] 6 19 profile20_node266_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36,192] 6 19 profile20_node266_cert).mp (by decide +kernel))

def profile20_node251_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node251_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node251 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,36] 6 (by decide) (choices 2) [3,17,18,65,66,80,192] profile20_node251_route profile20_node251_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node252
  · exact profile20_node253
  · exact profile20_node258
  · exact profile20_node263
  · exact profile20_node264
  · exact profile20_node265
  · exact profile20_node266

def profile20_node268_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 50 7 220 212 244 64 128), lower := (rows 193 50 7 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 32 255 255), good := (rows 193 231 199 201 193 225 193 193) }] }

theorem profile20_node268 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,3] 6 212 profile20_node268_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,3] 6 212 profile20_node268_cert).mp (by decide +kernel))

def profile20_node271_cert : CutBound 8 := { lost := (rows 16 64 0 64 0 0 0 0), upper := (rows 193 50 21 14 80 160 64 128), lower := (rows 193 50 21 14 80 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 255 255 255), good := (rows 225 227 229 239 225 225 225 225) },{ target := 6, region := (rows 1 22 4 12 16 255 0 255), good := (rows 161 178 191 174 178 160 160 160) }] }

theorem profile20_node271 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,6,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,6,64] 6 128 profile20_node271_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,6,64] 6 128 profile20_node271_cert).mp (by decide +kernel))

def profile20_node270_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile20_node270_route : Route 8 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node270 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,6] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,6] 6 (by decide) (choices 1) [64] profile20_node270_route profile20_node270_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node271

def profile20_node272_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 50 21 74 148 164 64 128), lower := (rows 193 50 21 74 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 36 255 255), good := (rows 193 235 229 203 193 225 193 193) }] }

theorem profile20_node272 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,66] 6 132 profile20_node272_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,66] 6 132 profile20_node272_cert).mp (by decide +kernel))

def profile20_node273_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 50 21 76 146 162 64 128), lower := (rows 193 50 21 76 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 12 0 34 255 255), good := (rows 193 227 205 205 193 225 193 193) }] }

theorem profile20_node273 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,68] 6 130 profile20_node273_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,68] 6 130 profile20_node273_cert).mp (by decide +kernel))

def profile20_node274_cert : Bound 8 := { allowed := (rows 16 192 192 16 0 0 0 0), upper := (rows 193 50 21 200 22 38 64 128), lower := (rows 193 50 21 200 16 32 64 128), losses := [] }

theorem profile20_node274 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,192] 6 6 profile20_node274_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17,192] 6 6 profile20_node274_cert).mp (by decide +kernel))

def profile20_node269_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node269_route : Route 8 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node269 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,17] 6 (by decide) (choices 2) [6,66,68,192] profile20_node269_route profile20_node269_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node270
  · exact profile20_node272
  · exact profile20_node273
  · exact profile20_node274

def profile20_node275_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 50 22 205 213 229 64 128), lower := (rows 193 50 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 12 0 36 255 255), good := (rows 193 227 239 201 193 225 193 193) }] }

theorem profile20_node275 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,18] 6 197 profile20_node275_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,18] 6 197 profile20_node275_cert).mp (by decide +kernel))

def profile20_node276_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 50 69 158 150 182 64 128), lower := (rows 193 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) }] }

theorem profile20_node276 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,65] 6 150 profile20_node276_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,65] 6 150 profile20_node276_cert).mp (by decide +kernel))

def profile20_node277_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 50 70 157 149 181 64 128), lower := (rows 193 50 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 32 255 255), good := (rows 193 231 199 201 193 225 193 193) }] }

theorem profile20_node277 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,66] 6 149 profile20_node277_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,66] 6 149 profile20_node277_cert).mp (by decide +kernel))

def profile20_node278_cert : Bound 8 := { allowed := (rows 0 192 128 208 0 0 0 0), upper := (rows 193 50 84 143 151 167 64 128), lower := (rows 193 50 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 227 197 201 193 225 193 193) }] }

theorem profile20_node278 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,80] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,80] 6 135 profile20_node278_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,80] 6 135 profile20_node278_cert).mp (by decide +kernel))

def profile20_node279_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 50 196 31 23 55 64 128), lower := (rows 193 50 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) }] }

theorem profile20_node279 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,192] 6 23 profile20_node279_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48,192] 6 23 profile20_node279_cert).mp (by decide +kernel))

def profile20_node267_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile20_node267_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node267 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,48] 6 (by decide) (choices 2) [3,17,18,65,66,80,192] profile20_node267_route profile20_node267_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node268
  · exact profile20_node269
  · exact profile20_node275
  · exact profile20_node276
  · exact profile20_node277
  · exact profile20_node278
  · exact profile20_node279

def profile20_node280_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 67 182 190 182 182 64 128), lower := (rows 193 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) }] }

theorem profile20_node280 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,65] 6 182 profile20_node280_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,65] 6 182 profile20_node280_cert).mp (by decide +kernel))

def profile20_node281_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 70 183 187 179 179 64 128), lower := (rows 193 70 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 6 4 8 0 32 255 255), good := (rows 193 199 199 201 193 225 193 193) }] }

theorem profile20_node281 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,68] 6 179 profile20_node281_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,68] 6 179 profile20_node281_cert).mp (by decide +kernel))

def profile20_node282_cert : CutBound 8 := { lost := (rows 16 128 0 0 0 0 0 0), upper := (rows 193 82 183 191 183 183 64 128), lower := (rows 193 82 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) },{ target := 7, region := (rows 1 18 4 8 16 32 255 0), good := (rows 65 82 68 72 82 96 64 64) }] }

theorem profile20_node282 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,80] 6 183 profile20_node282_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,80] 6 183 profile20_node282_cert).mp (by decide +kernel))

def profile20_node283_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 98 151 159 151 183 64 128), lower := (rows 193 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 34 4 8 0 32 255 255), good := (rows 193 227 197 201 193 227 193 193) }] }

theorem profile20_node283 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,96] 6 151 profile20_node283_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,96] 6 151 profile20_node283_cert).mp (by decide +kernel))

def profile20_node284_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 194 55 63 55 55 64 128), lower := (rows 193 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) }] }

theorem profile20_node284 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,192] 6 55 profile20_node284_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192,192] 6 55 profile20_node284_cert).mp (by decide +kernel))

def profile20_node215_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node215_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node215 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [192] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] profile20_node215_route profile20_node215_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node216
  · exact profile20_node217
  · exact profile20_node234
  · exact profile20_node250
  · exact profile20_node251
  · exact profile20_node267
  · exact profile20_node280
  · exact profile20_node281
  · exact profile20_node282
  · exact profile20_node283
  · exact profile20_node284

def profile20_node0_column : Nat → Fin 8 := fun mask => match mask with | 10 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile20_node0_route : Route 8 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 68 => (66,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 132 => (66,(fun i => match i.val with | 1 => 2 | 2 => 1 | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile20_node0 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [] 6 (by decide) (choices 2) [6,18,34,48,66,80,96,192] profile20_node0_route profile20_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node1
  · exact profile20_node35
  · exact profile20_node77
  · exact profile20_node110
  · exact profile20_node149
  · exact profile20_node150
  · exact profile20_node214
  · exact profile20_node215

theorem profile20 : Upper (D (n:=8) [33,33,33,32,18,17,2,2]) (R (n:=8) [33,33,33,32,18,17,2,2]) [] 6 := profile20_node0


#print axioms profile20
end Delivery.SmallBudgetTenFinite8
