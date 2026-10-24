import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0220
import IrregularNine14P06C0221

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31200 : Route 9 := (fun mask => (mask,id))

def c31200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u31200 : Upper (D 6) (R 6) [10,36,66,132,33] 13 := by
  apply FastRouting.sound _ _ [10,36,66,132,33] 13 (by decide) (choices 1) [1,16,64,256] r31200 c31200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13210
  · exact u13211
  · exact u13212
  · exact u13213

def r31201 : Route 9 := (fun mask => (mask,id))

def c31201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31201 : Upper (D 6) (R 6) [10,36,66,132,65] 13 := by
  apply FastRouting.sound _ _ [10,36,66,132,65] 13 (by decide) (choices 1) [1,16,256] r31201 c31201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13214
  · exact u13215
  · exact u13216

def b31202 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 4, region := 6, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 70 140 112 305 337 401 273), lower := (rows 11 38 70 140 112 32 64 128 256), losses := [] }

theorem u31202 : Upper (D 6) (R 6) [10,36,66,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31203 : Route 9 := (fun mask => (mask,id))

def c31203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31203 : Upper (D 6) (R 6) [10,36,66,132,257] 13 := by
  apply FastRouting.sound _ _ [10,36,66,132,257] 13 (by decide) (choices 1) [1,16,64] r31203 c31203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13217
  · exact u13218
  · exact u13219

def r31204 : Route 9 := (fun mask => (mask,id))

def c31204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31204 : Upper (D 6) (R 6) [10,36,66,132,288] 13 := by
  apply FastRouting.sound _ _ [10,36,66,132,288] 13 (by decide) (choices 1) [1,16,64] r31204 c31204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13220
  · exact u13221
  · exact u13222

def r31205 : Route 9 := (fun mask => (mask,id))

def c31205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31205 : Upper (D 6) (R 6) [10,36,66,132,320] 13 := by
  apply FastRouting.sound _ _ [10,36,66,132,320] 13 (by decide) (choices 1) [1,16] r31205 c31205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13223
  · exact u13224

def r31206 : Route 9 := (fun mask => (mask,id))

def c31206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31206 : Upper (D 6) (R 6) [10,36,66,144,5] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144,5] 13 (by decide) (choices 1) [1,64,256] r31206 c31206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13225
  · exact u13226
  · exact u13227

def r31207 : Route 9 := (fun mask => (mask,id))

def c31207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31207 : Upper (D 6) (R 6) [10,36,66,144,33] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144,33] 13 (by decide) (choices 1) [1,4,64,256] r31207 c31207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13228
  · exact u13229
  · exact u13230
  · exact u13231

def b31208 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 70 152 52 353 321 449 321), lower := (rows 11 38 70 152 52 32 64 128 256), losses := [] }

theorem u31208 : Upper (D 6) (R 6) [10,36,66,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31209 : Route 9 := (fun mask => (mask,id))

def c31209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31209 : Upper (D 6) (R 6) [10,36,66,144,65] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144,65] 13 (by decide) (choices 1) [1,4,256] r31209 c31209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13232
  · exact u13233
  · exact u13234

def b31210 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 70 152 84 289 353 417 289), lower := (rows 11 38 70 152 84 32 64 128 256), losses := [] }

theorem u31210 : Upper (D 6) (R 6) [10,36,66,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31211 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 6, targets := 1 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 38 70 152 112 293 325 389 261), lower := (rows 11 38 70 152 112 32 64 128 256), losses := [] }

theorem u31211 : Upper (D 6) (R 6) [10,36,66,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31212 : Route 9 := (fun mask => (mask,id))

def c31212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31212 : Upper (D 6) (R 6) [10,36,66,144,257] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144,257] 13 (by decide) (choices 1) [1,4,64] r31212 c31212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13235
  · exact u13236
  · exact u13237

def r31213 : Route 9 := (fun mask => (mask,id))

def c31213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31213 : Upper (D 6) (R 6) [10,36,66,144,260] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144,260] 13 (by decide) (choices 1) [1,64] r31213 c31213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13238
  · exact u13239

def r31214 : Route 9 := (fun mask => (mask,id))

def c31214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31214 : Upper (D 6) (R 6) [10,36,66,144,288] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144,288] 13 (by decide) (choices 1) [1,4,64] r31214 c31214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13240
  · exact u13241
  · exact u13242

def r31215 : Route 9 := (fun mask => (mask,id))

def c31215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31215 : Upper (D 6) (R 6) [10,36,66,144,320] 13 := by
  apply FastRouting.sound _ _ [10,36,66,144,320] 13 (by decide) (choices 1) [1,4] r31215 c31215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13243
  · exact u13244

def b31216 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 488, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 38 70 168 21 369 337 465 337), lower := (rows 11 38 70 168 21 32 64 128 256), losses := [] }

theorem u31216 : Upper (D 6) (R 6) [10,36,66,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31217 : Route 9 := (fun mask => (mask,id))

def c31217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31217 : Upper (D 6) (R 6) [10,36,66,160,65] 13 := by
  apply FastRouting.sound _ _ [10,36,66,160,65] 13 (by decide) (choices 1) [1,4,16,256] r31217 c31217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13245
  · exact u13246
  · exact u13247
  · exact u13248

def b31218 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 70 168 84 305 337 401 273), lower := (rows 11 38 70 168 84 32 64 128 256), losses := [] }

theorem u31218 : Upper (D 6) (R 6) [10,36,66,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31219 : Route 9 := (fun mask => (mask,id))

def c31219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31219 : Upper (D 6) (R 6) [10,36,66,160,257] 13 := by
  apply FastRouting.sound _ _ [10,36,66,160,257] 13 (by decide) (choices 1) [1,4,16,64] r31219 c31219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13249
  · exact u13250
  · exact u13251
  · exact u13252

def r31220 : Route 9 := (fun mask => (mask,id))

def c31220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31220 : Upper (D 6) (R 6) [10,36,66,160,260] 13 := by
  apply FastRouting.sound _ _ [10,36,66,160,260] 13 (by decide) (choices 1) [1,16,64] r31220 c31220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13253
  · exact u13254
  · exact u13255

def r31221 : Route 9 := (fun mask => (mask,id))

def c31221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31221 : Upper (D 6) (R 6) [10,36,66,160,320] 13 := by
  apply FastRouting.sound _ _ [10,36,66,160,320] 13 (by decide) (choices 1) [1,4,16] r31221 c31221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13256
  · exact u13257
  · exact u13258

def b31222 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 488, targets := 6 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,6),(3,1),(3,2)], upper := (rows 11 38 70 200 21 305 369 433 305), lower := (rows 11 38 70 200 21 32 64 128 256), losses := [] }

theorem u31222 : Upper (D 6) (R 6) [10,36,66,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31223 : Route 9 := (fun mask => (mask,id))

def c31223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31223 : Upper (D 6) (R 6) [10,36,66,192,33] 13 := by
  apply FastRouting.sound _ _ [10,36,66,192,33] 13 (by decide) (choices 1) [1,4,16,256] r31223 c31223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13259
  · exact u13260
  · exact u13261
  · exact u13262

def b31224 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 70 200 52 305 337 401 273), lower := (rows 11 38 70 200 52 32 64 128 256), losses := [] }

theorem u31224 : Upper (D 6) (R 6) [10,36,66,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31225 : Route 9 := (fun mask => (mask,id))

def c31225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31225 : Upper (D 6) (R 6) [10,36,66,192,257] 13 := by
  apply FastRouting.sound _ _ [10,36,66,192,257] 13 (by decide) (choices 1) [1,4,16] r31225 c31225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13263
  · exact u13264
  · exact u13265

def r31226 : Route 9 := (fun mask => (mask,id))

def c31226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31226 : Upper (D 6) (R 6) [10,36,66,192,260] 13 := by
  apply FastRouting.sound _ _ [10,36,66,192,260] 13 (by decide) (choices 1) [1,16] r31226 c31226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13266
  · exact u13267

def r31227 : Route 9 := (fun mask => (mask,id))

def c31227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31227 : Upper (D 6) (R 6) [10,36,66,192,288] 13 := by
  apply FastRouting.sound _ _ [10,36,66,192,288] 13 (by decide) (choices 1) [1,4,16] r31227 c31227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13268
  · exact u13269
  · exact u13270

def r31228 : Route 9 := (fun mask => (mask,id))

def c31228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31228 : Upper (D 6) (R 6) [10,36,66,384,5] 13 := by
  apply FastRouting.sound _ _ [10,36,66,384,5] 13 (by decide) (choices 1) [1,16,64] r31228 c31228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13271
  · exact u13272
  · exact u13273

def r31229 : Route 9 := (fun mask => (mask,id))

def c31229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31229 : Upper (D 6) (R 6) [10,36,66,384,33] 13 := by
  apply FastRouting.sound _ _ [10,36,66,384,33] 13 (by decide) (choices 1) [1,4,16,64] r31229 c31229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13274
  · exact u13275
  · exact u13276
  · exact u13277

def b31230 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 70 392 52 113 81 209 337), lower := (rows 11 38 70 392 52 32 64 128 256), losses := [] }

theorem u31230 : Upper (D 6) (R 6) [10,36,66,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31231 : Route 9 := (fun mask => (mask,id))

def c31231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31231 : Upper (D 6) (R 6) [10,36,66,384,65] 13 := by
  apply FastRouting.sound _ _ [10,36,66,384,65] 13 (by decide) (choices 1) [1,4,16] r31231 c31231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13278
  · exact u13279
  · exact u13280

def b31232 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 70 392 84 49 113 177 305), lower := (rows 11 38 70 392 84 32 64 128 256), losses := [] }

theorem u31232 : Upper (D 6) (R 6) [10,36,66,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31233 : Route 9 := (fun mask => (mask,id))

def c31233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31233 : Upper (D 6) (R 6) [10,36,66,384,96] 13 := by
  apply FastRouting.sound _ _ [10,36,66,384,96] 13 (by decide) (choices 1) [1,4,16] r31233 c31233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13281
  · exact u13282
  · exact u13283

def b31234 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 84 73 19 420 484 420 420), lower := (rows 11 38 84 73 19 32 64 128 256), losses := [] }

theorem u31234 : Upper (D 6) (R 6) [10,36,80,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31235 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 20, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 84 73 21 418 482 418 418), lower := (rows 11 38 84 73 21 32 64 128 256), losses := [] }

theorem u31235 : Upper (D 6) (R 6) [10,36,80,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31236 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 84 73 22 417 481 417 417), lower := (rows 11 38 84 73 22 32 64 128 256), losses := [] }

theorem u31236 : Upper (D 6) (R 6) [10,36,80,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31237 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 4, region := 454, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 84 73 49 422 454 390 390), lower := (rows 11 38 84 73 49 32 64 128 256), losses := [] }

theorem u31237 : Upper (D 6) (R 6) [10,36,80,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31238 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 84 73 50 421 453 389 389), lower := (rows 11 38 84 73 50 32 64 128 256), losses := [] }

theorem u31238 : Upper (D 6) (R 6) [10,36,80,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31239 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 1, region := 457, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 38 84 73 52 419 451 387 387), lower := (rows 11 38 84 73 52 32 64 128 256), losses := [] }

theorem u31239 : Upper (D 6) (R 6) [10,36,80,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31240 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 2, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 84 73 145 294 358 422 294), lower := (rows 11 38 84 73 145 32 64 128 256), losses := [] }

theorem u31240 : Upper (D 6) (R 6) [10,36,80,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31241 : Route 9 := (fun mask => (mask,id))

def c31241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31241 : Upper (D 6) (R 6) [10,36,80,65,130] 13 := by
  apply FastRouting.sound _ _ [10,36,80,65,130] 13 (by decide) (choices 1) [1,4,256] r31241 c31241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13284
  · exact u13285
  · exact u13286

def r31242 : Route 9 := (fun mask => (mask,id))

def c31242 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31242 : Upper (D 6) (R 6) [10,36,80,65,132] 13 := by
  apply FastRouting.sound _ _ [10,36,80,65,132] 13 (by decide) (choices 1) [1,2,256] r31242 c31242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13287
  · exact u13288
  · exact u13289

def r31243 : Route 9 := (fun mask => (mask,id))

def c31243 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31243 : Upper (D 6) (R 6) [10,36,80,65,160] 13 := by
  apply FastRouting.sound _ _ [10,36,80,65,160] 13 (by decide) (choices 1) [1,2,4,256] r31243 c31243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13290
  · exact u13291
  · exact u13292
  · exact u13293

def r31244 : Route 9 := (fun mask => (mask,id))

def c31244 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31244 : Upper (D 6) (R 6) [10,36,80,65,384] 13 := by
  apply FastRouting.sound _ _ [10,36,80,65,384] 13 (by decide) (choices 1) [1,2,4] r31244 c31244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13294
  · exact u13295
  · exact u13296

def b31245 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 38 84 104 19 421 453 389 389), lower := (rows 11 38 84 104 19 32 64 128 256), losses := [] }

theorem u31245 : Upper (D 6) (R 6) [10,36,80,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31246 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 457, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 84 104 21 419 451 387 387), lower := (rows 11 38 84 104 21 32 64 128 256), losses := [] }

theorem u31246 : Upper (D 6) (R 6) [10,36,80,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31247 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 84 104 22 417 449 385 385), lower := (rows 11 38 84 104 22 32 64 128 256), losses := [] }

theorem u31247 : Upper (D 6) (R 6) [10,36,80,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31248 : Route 9 := (fun mask => (mask,id))

def c31248 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31248 : Upper (D 6) (R 6) [10,36,80,96,129] 13 := by
  apply FastRouting.sound _ _ [10,36,80,96,129] 13 (by decide) (choices 1) [1,2,4,256] r31248 c31248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13297
  · exact u13298
  · exact u13299
  · exact u13300

def r31249 : Route 9 := (fun mask => (mask,id))

def c31249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31249 : Upper (D 6) (R 6) [10,36,80,96,130] 13 := by
  apply FastRouting.sound _ _ [10,36,80,96,130] 13 (by decide) (choices 1) [1,4,256] r31249 c31249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13301
  · exact u13302
  · exact u13303

def b31250 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 84 104 148 291 323 387 259), lower := (rows 11 38 84 104 148 32 64 128 256), losses := [] }

theorem u31250 : Upper (D 6) (R 6) [10,36,80,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31251 : Route 9 := (fun mask => (mask,id))

def c31251 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31251 : Upper (D 6) (R 6) [10,36,80,96,384] 13 := by
  apply FastRouting.sound _ _ [10,36,80,96,384] 13 (by decide) (choices 1) [1,2,4] r31251 c31251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13304
  · exact u13305
  · exact u13306

def b31252 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 84 137 19 356 356 484 356), lower := (rows 11 38 84 137 19 32 64 128 256), losses := [] }

theorem u31252 : Upper (D 6) (R 6) [10,36,80,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31253 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 457, targets := 4 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 84 137 21 354 354 482 354), lower := (rows 11 38 84 137 21 32 64 128 256), losses := [] }

theorem u31253 : Upper (D 6) (R 6) [10,36,80,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31254 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 84 137 22 353 353 481 353), lower := (rows 11 38 84 137 22 32 64 128 256), losses := [] }

theorem u31254 : Upper (D 6) (R 6) [10,36,80,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31255 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 4, region := 326, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 84 137 49 358 326 454 326), lower := (rows 11 38 84 137 49 32 64 128 256), losses := [] }

theorem u31255 : Upper (D 6) (R 6) [10,36,80,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31256 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 84 137 50 357 325 453 325), lower := (rows 11 38 84 137 50 32 64 128 256), losses := [] }

theorem u31256 : Upper (D 6) (R 6) [10,36,80,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31257 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 1, region := 457, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 38 84 137 52 355 323 451 323), lower := (rows 11 38 84 137 52 32 64 128 256), losses := [] }

theorem u31257 : Upper (D 6) (R 6) [10,36,80,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31258 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 137 81 294 358 422 294), lower := (rows 11 38 84 137 81 32 64 128 256), losses := [] }

theorem u31258 : Upper (D 6) (R 6) [10,36,80,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31259 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 137 82 293 357 421 293), lower := (rows 11 38 84 137 82 32 64 128 256), losses := [] }

theorem u31259 : Upper (D 6) (R 6) [10,36,80,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u31259
end Delivery.IrregularNine14.P06
