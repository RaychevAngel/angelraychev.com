import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0253
import IrregularNine14P07C0254
import IrregularNine14P07C0255

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32160 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 74 145 184 248 184 440), lower := (rows 7 290 69 74 145 32 64 128 256), losses := [] }

theorem u32160 : Upper (D 7) (R 7) [6,288,65,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32161 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 74 152 177 241 177 433), lower := (rows 7 290 69 74 152 32 64 128 256), losses := [] }

theorem u32161 : Upper (D 7) (R 7) [6,288,65,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32162 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 74 176 185 217 153 409), lower := (rows 7 290 69 74 176 32 64 128 256), losses := [] }

theorem u32162 : Upper (D 7) (R 7) [6,288,65,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32163 : Route 9 := (fun mask => (mask,id))

def c32163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32163 : Upper (D 7) (R 7) [6,288,65,80,129] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80,129] 13 (by decide) (choices 1) [2,8,128] r32163 c32163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15227
  · exact u15228
  · exact u15229

def r32164 : Route 9 := (fun mask => (mask,id))

def c32164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32164 : Upper (D 7) (R 7) [6,288,65,80,130] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80,130] 13 (by decide) (choices 1) [1,8,128] r32164 c32164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15230
  · exact u15231
  · exact u15232

def r32165 : Route 9 := (fun mask => (mask,id))

def c32165 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32165 : Upper (D 7) (R 7) [6,288,65,80,136] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80,136] 13 (by decide) (choices 1) [1,2,128] r32165 c32165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15233
  · exact u15234
  · exact u15235

def r32166 : Route 9 := (fun mask => (mask,id))

def c32166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32166 : Upper (D 7) (R 7) [6,288,65,80,160] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80,160] 13 (by decide) (choices 1) [1,2,8,128] r32166 c32166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15236
  · exact u15237
  · exact u15238
  · exact u15239

def r32167 : Route 9 := (fun mask => (mask,id))

def c32167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32167 : Upper (D 7) (R 7) [6,288,65,96,129] 13 := by
  apply FastRouting.sound _ _ [6,288,65,96,129] 13 (by decide) (choices 1) [2,8,16,128] r32167 c32167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15240
  · exact u15241
  · exact u15242
  · exact u15243

def r32168 : Route 9 := (fun mask => (mask,id))

def c32168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32168 : Upper (D 7) (R 7) [6,288,65,96,130] 13 := by
  apply FastRouting.sound _ _ [6,288,65,96,130] 13 (by decide) (choices 1) [1,8,16,128] r32168 c32168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15244
  · exact u15245
  · exact u15246
  · exact u15247

def r32169 : Route 9 := (fun mask => (mask,id))

def c32169 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32169 : Upper (D 7) (R 7) [6,288,65,96,136] 13 := by
  apply FastRouting.sound _ _ [6,288,65,96,136] 13 (by decide) (choices 1) [1,2,16,128] r32169 c32169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15248
  · exact u15249
  · exact u15250
  · exact u15251

def r32170 : Route 9 := (fun mask => (mask,id))

def c32170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32170 : Upper (D 7) (R 7) [6,288,65,129,130] 13 := by
  apply FastRouting.sound _ _ [6,288,65,129,130] 13 (by decide) (choices 1) [8,16,64] r32170 c32170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15252
  · exact u15253
  · exact u15254

def b32171 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7),(4,1),(4,5),(4,6)], upper := (rows 7 290 69 137 152 114 114 242 370), lower := (rows 7 290 69 137 152 32 64 128 256), losses := [] }

theorem u32171 : Upper (D 7) (R 7) [6,288,65,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32172 : Route 9 := (fun mask => (mask,id))

def c32172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32172 : Upper (D 7) (R 7) [6,288,65,129,160] 13 := by
  apply FastRouting.sound _ _ [6,288,65,129,160] 13 (by decide) (choices 1) [2,8,16,64] r32172 c32172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15255
  · exact u15256
  · exact u15257
  · exact u15258

def r32173 : Route 9 := (fun mask => (mask,id))

def c32173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32173 : Upper (D 7) (R 7) [6,288,65,129,192] 13 := by
  apply FastRouting.sound _ _ [6,288,65,129,192] 13 (by decide) (choices 1) [2,8,16] r32173 c32173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15259
  · exact u15260
  · exact u15261

def b32174 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 7 290 69 138 152 113 113 241 369), lower := (rows 7 290 69 138 152 32 64 128 256), losses := [] }

theorem u32174 : Upper (D 7) (R 7) [6,288,65,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32175 : Route 9 := (fun mask => (mask,id))

def c32175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32175 : Upper (D 7) (R 7) [6,288,65,130,160] 13 := by
  apply FastRouting.sound _ _ [6,288,65,130,160] 13 (by decide) (choices 1) [1,8,16,64] r32175 c32175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15262
  · exact u15263
  · exact u15264
  · exact u15265

def r32176 : Route 9 := (fun mask => (mask,id))

def c32176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32176 : Upper (D 7) (R 7) [6,288,65,130,192] 13 := by
  apply FastRouting.sound _ _ [6,288,65,130,192] 13 (by decide) (choices 1) [1,8,16] r32176 c32176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15266
  · exact u15267
  · exact u15268

def b32177 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 290 69 152 152 99 99 227 355), lower := (rows 7 290 69 152 152 32 64 128 256), losses := [] }

theorem u32177 : Upper (D 7) (R 7) [6,288,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32178 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 290 69 152 176 107 75 203 331), lower := (rows 7 290 69 152 176 32 64 128 256), losses := [] }

theorem u32178 : Upper (D 7) (R 7) [6,288,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32179 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 290 69 152 208 43 107 171 299), lower := (rows 7 290 69 152 208 32 64 128 256), losses := [] }

theorem u32179 : Upper (D 7) (R 7) [6,288,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32180 : Route 9 := (fun mask => (mask,id))

def c32180 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32180 : Upper (D 7) (R 7) [6,288,65,160,192] 13 := by
  apply FastRouting.sound _ _ [6,288,65,160,192] 13 (by decide) (choices 1) [1,2,8,16] r32180 c32180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15269
  · exact u15270
  · exact u15271
  · exact u15272

def b32181 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 290 76 25 19 224 224 224 480), lower := (rows 7 290 76 25 19 32 64 128 256), losses := [] }

theorem u32181 : Upper (D 7) (R 7) [6,288,72,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32182 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 76 25 49 226 194 194 450), lower := (rows 7 290 76 25 49 32 64 128 256), losses := [] }

theorem u32182 : Upper (D 7) (R 7) [6,288,72,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32183 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 290 76 25 50 225 193 193 449), lower := (rows 7 290 76 25 50 32 64 128 256), losses := [] }

theorem u32183 : Upper (D 7) (R 7) [6,288,72,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32184 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 7 290 76 25 81 162 226 162 418), lower := (rows 7 290 76 25 81 32 64 128 256), losses := [] }

theorem u32184 : Upper (D 7) (R 7) [6,288,72,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32185 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 25 82 161 225 161 417), lower := (rows 7 290 76 25 82 32 64 128 256), losses := [] }

theorem u32185 : Upper (D 7) (R 7) [6,288,72,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32186 : Route 9 := (fun mask => (mask,id))

def c32186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32186 : Upper (D 7) (R 7) [6,288,72,17,96] 13 := by
  apply FastRouting.sound _ _ [6,288,72,17,96] 13 (by decide) (choices 1) [1,2,128] r32186 c32186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15273
  · exact u15274
  · exact u15275

def b32187 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 76 25 145 226 226 226 482), lower := (rows 7 290 76 25 145 32 64 128 256), losses := [] }

theorem u32187 : Upper (D 7) (R 7) [6,288,72,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32188 : Route 9 := (fun mask => (mask,id))

def c32188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32188 : Upper (D 7) (R 7) [6,288,72,17,130] 13 := by
  apply FastRouting.sound _ _ [6,288,72,17,130] 13 (by decide) (choices 1) [1,64,128] r32188 c32188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15276
  · exact u15277
  · exact u15278

def r32189 : Route 9 := (fun mask => (mask,id))

def c32189 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32189 : Upper (D 7) (R 7) [6,288,72,17,160] 13 := by
  apply FastRouting.sound _ _ [6,288,72,17,160] 13 (by decide) (choices 1) [1,2,64,128] r32189 c32189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15279
  · exact u15280
  · exact u15281
  · exact u15282

def r32190 : Route 9 := (fun mask => (mask,id))

def c32190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32190 : Upper (D 7) (R 7) [6,288,72,17,192] 13 := by
  apply FastRouting.sound _ _ [6,288,72,17,192] 13 (by decide) (choices 1) [1,2,128] r32190 c32190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15283
  · exact u15284
  · exact u15285

def b32191 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 197, targets := 32 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,5),(2,1),(2,5),(4,1)], upper := (rows 7 290 76 26 49 225 193 193 449), lower := (rows 7 290 76 26 49 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 501 288 76 508 497 32 64 128 256) }] }

theorem u32191 : Upper (D 7) (R 7) [6,288,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32192 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 240, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,1)], upper := (rows 7 290 76 26 81 161 225 161 417), lower := (rows 7 290 76 26 81 32 64 128 256), losses := [] }

theorem u32192 : Upper (D 7) (R 7) [6,288,72,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32193 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(0,6),(1,6),(2,5)], upper := (rows 7 290 76 26 112 161 193 129 385), lower := (rows 7 290 76 26 112 32 64 128 256), losses := [] }

theorem u32193 : Upper (D 7) (R 7) [6,288,72,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32194 : Route 9 := (fun mask => (mask,id))

def c32194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32194 : Upper (D 7) (R 7) [6,288,72,18,129] 13 := by
  apply FastRouting.sound _ _ [6,288,72,18,129] 13 (by decide) (choices 1) [1,64,128] r32194 c32194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15286
  · exact u15287
  · exact u15288

def r32195 : Route 9 := (fun mask => (mask,id))

def c32195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32195 : Upper (D 7) (R 7) [6,288,72,18,160] 13 := by
  apply FastRouting.sound _ _ [6,288,72,18,160] 13 (by decide) (choices 1) [1,64,128] r32195 c32195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15289
  · exact u15290
  · exact u15291

def r32196 : Route 9 := (fun mask => (mask,id))

def c32196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32196 : Upper (D 7) (R 7) [6,288,72,18,192] 13 := by
  apply FastRouting.sound _ _ [6,288,72,18,192] 13 (by decide) (choices 1) [1,128] r32196 c32196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15292
  · exact u15293

def b32197 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 290 76 41 19 240 208 208 464), lower := (rows 7 290 76 41 19 32 64 128 256), losses := [] }

theorem u32197 : Upper (D 7) (R 7) [6,288,72,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32198 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(1,6),(3,6),(4,5)], upper := (rows 7 290 76 41 81 178 210 146 402), lower := (rows 7 290 76 41 81 32 64 128 256), losses := [] }

theorem u32198 : Upper (D 7) (R 7) [6,288,72,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32199 : Route 9 := (fun mask => (mask,id))

def c32199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32199 : Upper (D 7) (R 7) [6,288,72,33,66] 13 := by
  apply FastRouting.sound _ _ [6,288,72,33,66] 13 (by decide) (choices 1) [1,16,128] r32199 c32199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15294
  · exact u15295
  · exact u15296

def r32200 : Route 9 := (fun mask => (mask,id))

def c32200 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32200 : Upper (D 7) (R 7) [6,288,72,33,129] 13 := by
  apply FastRouting.sound _ _ [6,288,72,33,129] 13 (by decide) (choices 1) [2,16,64,128] r32200 c32200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15297
  · exact u15298
  · exact u15299
  · exact u15300

def r32201 : Route 9 := (fun mask => (mask,id))

def c32201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32201 : Upper (D 7) (R 7) [6,288,72,33,130] 13 := by
  apply FastRouting.sound _ _ [6,288,72,33,130] 13 (by decide) (choices 1) [1,16,64,128] r32201 c32201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15301
  · exact u15302
  · exact u15303
  · exact u15304

def r32202 : Route 9 := (fun mask => (mask,id))

def c32202 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32202 : Upper (D 7) (R 7) [6,288,72,33,192] 13 := by
  apply FastRouting.sound _ _ [6,288,72,33,192] 13 (by decide) (choices 1) [1,2,16,128] r32202 c32202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15305
  · exact u15306
  · exact u15307
  · exact u15308

def b32203 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 290 76 56 19 225 193 193 449), lower := (rows 7 290 76 56 19 32 64 128 256), losses := [] }

theorem u32203 : Upper (D 7) (R 7) [6,288,72,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32204 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,5)], upper := (rows 7 290 76 56 81 163 195 131 387), lower := (rows 7 290 76 56 81 32 64 128 256), losses := [] }

theorem u32204 : Upper (D 7) (R 7) [6,288,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32205 : Route 9 := (fun mask => (mask,id))

def c32205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32205 : Upper (D 7) (R 7) [6,288,72,48,66] 13 := by
  apply FastRouting.sound _ _ [6,288,72,48,66] 13 (by decide) (choices 1) [1,128] r32205 c32205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15309
  · exact u15310

def r32206 : Route 9 := (fun mask => (mask,id))

def c32206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32206 : Upper (D 7) (R 7) [6,288,72,48,129] 13 := by
  apply FastRouting.sound _ _ [6,288,72,48,129] 13 (by decide) (choices 1) [1,2,64,128] r32206 c32206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15311
  · exact u15312
  · exact u15313
  · exact u15314

def r32207 : Route 9 := (fun mask => (mask,id))

def c32207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32207 : Upper (D 7) (R 7) [6,288,72,48,130] 13 := by
  apply FastRouting.sound _ _ [6,288,72,48,130] 13 (by decide) (choices 1) [1,64,128] r32207 c32207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15315
  · exact u15316
  · exact u15317

def r32208 : Route 9 := (fun mask => (mask,id))

def c32208 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32208 : Upper (D 7) (R 7) [6,288,72,48,192] 13 := by
  apply FastRouting.sound _ _ [6,288,72,48,192] 13 (by decide) (choices 1) [1,2,128] r32208 c32208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15318
  · exact u15319
  · exact u15320

def b32209 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 290 76 137 19 240 240 240 496), lower := (rows 7 290 76 137 19 32 64 128 256), losses := [] }

theorem u32209 : Upper (D 7) (R 7) [6,288,72,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32210 : Route 9 := (fun mask => (mask,id))

def c32210 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32210 : Upper (D 7) (R 7) [6,288,72,129,33] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,33] 13 (by decide) (choices 1) [2,16,64,128] r32210 c32210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15321
  · exact u15322
  · exact u15323
  · exact u15324

def b32211 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 290 76 137 50 241 209 209 465), lower := (rows 7 290 76 137 50 32 64 128 256), losses := [] }

theorem u32211 : Upper (D 7) (R 7) [6,288,72,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32212 : Route 9 := (fun mask => (mask,id))

def c32212 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32212 : Upper (D 7) (R 7) [6,288,72,129,65] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,65] 13 (by decide) (choices 1) [2,16,128] r32212 c32212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15325
  · exact u15326
  · exact u15327

def r32213 : Route 9 := (fun mask => (mask,id))

def c32213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32213 : Upper (D 7) (R 7) [6,288,72,129,66] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,66] 13 (by decide) (choices 1) [1,16,128] r32213 c32213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15328
  · exact u15329
  · exact u15330

def r32214 : Route 9 := (fun mask => (mask,id))

def c32214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32214 : Upper (D 7) (R 7) [6,288,72,129,96] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,96] 13 (by decide) (choices 1) [1,2,16,128] r32214 c32214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15331
  · exact u15332
  · exact u15333
  · exact u15334

def b32215 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 7 290 76 137 145 114 114 242 370), lower := (rows 7 290 76 137 145 32 64 128 256), losses := [] }

theorem u32215 : Upper (D 7) (R 7) [6,288,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32216 : Route 9 := (fun mask => (mask,id))

def c32216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32216 : Upper (D 7) (R 7) [6,288,72,129,130] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,130] 13 (by decide) (choices 1) [1,16,64] r32216 c32216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15335
  · exact u15336
  · exact u15337

def r32217 : Route 9 := (fun mask => (mask,id))

def c32217 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32217 : Upper (D 7) (R 7) [6,288,72,129,160] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,160] 13 (by decide) (choices 1) [1,2,16,64] r32217 c32217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15338
  · exact u15339
  · exact u15340
  · exact u15341

def r32218 : Route 9 := (fun mask => (mask,id))

def c32218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32218 : Upper (D 7) (R 7) [6,288,72,129,192] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,192] 13 (by decide) (choices 1) [1,2,16] r32218 c32218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15342
  · exact u15343
  · exact u15344

def r32219 : Route 9 := (fun mask => (mask,id))

def c32219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32219 : Upper (D 7) (R 7) [6,288,72,130,33] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,33] 13 (by decide) (choices 1) [1,16,64,128] r32219 c32219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15345
  · exact u15346
  · exact u15347
  · exact u15348

#print axioms u32219
end Delivery.IrregularNine14.P07
