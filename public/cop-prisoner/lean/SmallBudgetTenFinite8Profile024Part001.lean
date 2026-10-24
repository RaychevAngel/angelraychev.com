import SmallBudgetTenFinite8Profile024Part000

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile24_node131_cert : CutBound 8 := { lost := (rows 48 0 32 16 0 0 0 0), upper := (rows 193 50 22 233 241 225 64 128), lower := (rows 193 50 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 239 233 233 233 233 233) },{ target := 5, region := (rows 255 2 6 8 16 0 255 255), good := (rows 193 215 215 201 209 193 193 193) }] }

theorem profile24_node131 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,18] 6 225 profile24_node131_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,18] 6 225 profile24_node131_cert).mp (by decide +kernel))

def profile24_node132_cert : CutBound 8 := { lost := (rows 48 0 0 48 0 0 0 0), upper := (rows 193 50 52 203 211 227 64 128), lower := (rows 193 50 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 34 255 255), good := (rows 193 235 229 201 193 225 193 193) },{ target := 5, region := (rows 255 2 4 10 18 0 255 255), good := (rows 193 219 213 201 209 193 193 193) }] }

theorem profile24_node132 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,48] 6 195 profile24_node132_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,48] 6 195 profile24_node132_cert).mp (by decide +kernel))

def profile24_node133_cert : CutBound 8 := { lost := (rows 48 0 48 0 0 0 0 0), upper := (rows 193 50 69 186 178 178 64 128), lower := (rows 193 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) },{ target := 5, region := (rows 255 2 255 8 16 0 255 255), good := (rows 197 215 197 205 213 197 197 197) }] }

theorem profile24_node133 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,65] 6 178 profile24_node133_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,65] 6 178 profile24_node133_cert).mp (by decide +kernel))

def profile24_node134_cert : CutBound 8 := { lost := (rows 48 0 48 0 0 0 0 0), upper := (rows 193 50 70 185 177 177 64 128), lower := (rows 193 50 70 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 32 255 255), good := (rows 193 231 199 201 193 225 193 193) },{ target := 5, region := (rows 255 2 6 8 16 0 255 255), good := (rows 193 215 199 201 209 193 193 193) }] }

theorem profile24_node134 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,66] 6 177 profile24_node134_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,66] 6 177 profile24_node134_cert).mp (by decide +kernel))

def profile24_node135_cert : CutBound 8 := { lost := (rows 48 0 32 16 0 0 0 0), upper := (rows 193 50 84 171 179 163 64 128), lower := (rows 193 50 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 34 255 255), good := (rows 193 235 197 201 193 225 193 193) },{ target := 5, region := (rows 255 2 22 8 16 0 255 255), good := (rows 193 215 213 201 213 193 193 193) }] }

theorem profile24_node135 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,80] 6 163 profile24_node135_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,80] 6 163 profile24_node135_cert).mp (by decide +kernel))

def profile24_node136_cert : CutBound 8 := { lost := (rows 48 0 48 0 0 0 0 0), upper := (rows 193 50 196 59 51 51 64 128), lower := (rows 193 50 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) },{ target := 5, region := (rows 255 2 255 8 16 0 255 255), good := (rows 197 215 197 205 213 197 197 197) }] }

theorem profile24_node136 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,192] 6 51 profile24_node136_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48,192] 6 51 profile24_node136_cert).mp (by decide +kernel))

def profile24_node128_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node128_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node128 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,48] 6 (by decide) (choices 2) [3,17,18,48,65,66,80,192] profile24_node128_route profile24_node128_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node129
  · exact profile24_node130
  · exact profile24_node131
  · exact profile24_node132
  · exact profile24_node133
  · exact profile24_node134
  · exact profile24_node135
  · exact profile24_node136

def profile24_node137_cert : CutBound 8 := { lost := (rows 48 48 0 0 0 0 0 0), upper := (rows 193 67 182 186 178 178 64 128), lower := (rows 193 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 5, region := (rows 255 255 4 8 16 0 255 255), good := (rows 195 195 199 203 211 195 195 195) }] }

theorem profile24_node137 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,65] 6 178 profile24_node137_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,65] 6 178 profile24_node137_cert).mp (by decide +kernel))

def profile24_node138_cert : CutBound 8 := { lost := (rows 48 160 0 0 0 0 0 0), upper := (rows 193 82 183 187 179 179 64 128), lower := (rows 193 82 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) },{ target := 5, region := (rows 255 18 4 8 16 0 255 255), good := (rows 193 211 197 201 211 193 193 193) },{ target := 7, region := (rows 1 18 4 8 16 32 255 0), good := (rows 65 82 68 72 82 96 64 64) }] }

theorem profile24_node138 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,80] 6 179 profile24_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,80] 6 179 profile24_node138_cert).mp (by decide +kernel))

def profile24_node139_cert : CutBound 8 := { lost := (rows 48 48 0 0 0 0 0 0), upper := (rows 193 194 55 59 51 51 64 128), lower := (rows 193 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) },{ target := 5, region := (rows 255 255 4 8 16 0 255 255), good := (rows 195 195 199 203 211 195 195 195) }] }

theorem profile24_node139 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,192] 6 51 profile24_node139_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192,192] 6 51 profile24_node139_cert).mp (by decide +kernel))

def profile24_node115_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node115_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node115 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [192] 6 (by decide) (choices 2) [17,48,65,80,192] profile24_node115_route profile24_node115_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile24_node116
  · exact profile24_node128
  · exact profile24_node137
  · exact profile24_node138
  · exact profile24_node139

def profile24_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile24_node0_route : Route 8 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile24_node0 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [] 6 (by decide) (choices 2) [18,48,66,80,192] profile24_node0_route profile24_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile24_node1
  · exact profile24_node38
  · exact profile24_node69
  · exact profile24_node84
  · exact profile24_node115

theorem profile24 : Upper (D (n:=8) [33,33,32,32,18,18,2,2]) (R (n:=8) [33,33,32,32,18,18,2,2]) [] 6 := profile24_node0


#print axioms profile24
end Delivery.SmallBudgetTenFinite8
