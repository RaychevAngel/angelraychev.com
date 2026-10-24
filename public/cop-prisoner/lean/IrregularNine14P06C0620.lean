import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0369
import IrregularNine14P06C0370
import IrregularNine14P06C0371
import IrregularNine14P06C0372

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37200 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 296 19 116 84 212 340), lower := (rows 35 131 76 296 19 32 64 128 256), losses := [] }

theorem u37200 : Upper (D 6) (R 6) [34,129,72,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37201 : Route 9 := (fun mask => (mask,id))

def c37201 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37201 : Upper (D 6) (R 6) [34,129,72,288,5] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288,5] 13 (by decide) (choices 1) [2,4,16,64] r37201 c37201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22181
  · exact u22182
  · exact u22183
  · exact u22184

def r37202 : Route 9 := (fun mask => (mask,id))

def c37202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37202 : Upper (D 6) (R 6) [34,129,72,288,6] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288,6] 13 (by decide) (choices 1) [1,4,16,64] r37202 c37202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22185
  · exact u22186
  · exact u22187
  · exact u22188

def r37203 : Route 9 := (fun mask => (mask,id))

def c37203 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37203 : Upper (D 6) (R 6) [34,129,72,288,65] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288,65] 13 (by decide) (choices 1) [2,4,16] r37203 c37203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22189
  · exact u22190
  · exact u22191

def r37204 : Route 9 := (fun mask => (mask,id))

def c37204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37204 : Upper (D 6) (R 6) [34,129,72,288,66] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288,66] 13 (by decide) (choices 1) [1,4,16] r37204 c37204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22192
  · exact u22193
  · exact u22194

def b37205 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 76 296 84 55 87 151 279), lower := (rows 35 131 76 296 84 32 64 128 256), losses := [] }

theorem u37205 : Upper (D 6) (R 6) [34,129,72,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37206 : PairBound 9 := { available := 340, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 11 28 372 340 468 340), lower := (rows 35 131 100 11 28 32 64 128 256), losses := [] }

theorem u37206 : Upper (D 6) (R 6) [34,129,96,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37207 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 11 88 308 340 404 276), lower := (rows 35 131 100 11 88 32 64 128 256), losses := [] }

theorem u37207 : Upper (D 6) (R 6) [34,129,96,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37208 : PairBound 9 := { available := 92, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 11 276 124 92 220 348), lower := (rows 35 131 100 11 276 32 64 128 256), losses := [] }

theorem u37208 : Upper (D 6) (R 6) [34,129,96,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37209 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 11 280 116 84 212 340), lower := (rows 35 131 100 11 280 32 64 128 256), losses := [] }

theorem u37209 : Upper (D 6) (R 6) [34,129,96,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37210 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 11 336 60 92 156 284), lower := (rows 35 131 100 11 336 32 64 128 256), losses := [] }

theorem u37210 : Upper (D 6) (R 6) [34,129,96,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37211 : Route 9 := (fun mask => (mask,id))

def c37211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u37211 : Upper (D 6) (R 6) [34,129,96,5,6] 13 := by
  apply FastRouting.sound _ _ [34,129,96,5,6] 13 (by decide) (choices 1) [8,16,64,256] r37211 c37211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22195
  · exact u22196
  · exact u22197
  · exact u22198

def b37212 : PairBound 9 := { available := 340, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 356, targets := 1 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 35 131 100 13 26 372 340 468 340), lower := (rows 35 131 100 13 26 32 64 128 256), losses := [] }

theorem u37212 : Upper (D 6) (R 6) [34,129,96,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37213 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 100 13 28 370 338 466 338), lower := (rows 35 131 100 13 28 32 64 128 256), losses := [] }

theorem u37213 : Upper (D 6) (R 6) [34,129,96,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37214 : Route 9 := (fun mask => (mask,id))

def c37214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37214 : Upper (D 6) (R 6) [34,129,96,5,66] 13 := by
  apply FastRouting.sound _ _ [34,129,96,5,66] 13 (by decide) (choices 1) [4,8,16,256] r37214 c37214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22199
  · exact u22200
  · exact u22201
  · exact u22202

def b37215 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 100 13 84 314 346 410 282), lower := (rows 35 131 100 13 84 32 64 128 256), losses := [] }

theorem u37215 : Upper (D 6) (R 6) [34,129,96,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37216 : Route 9 := (fun mask => (mask,id))

def c37216 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37216 : Upper (D 6) (R 6) [34,129,96,5,72] 13 := by
  apply FastRouting.sound _ _ [34,129,96,5,72] 13 (by decide) (choices 1) [2,4,16,256] r37216 c37216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22203
  · exact u22204
  · exact u22205
  · exact u22206

def r37217 : Route 9 := (fun mask => (mask,id))

def c37217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37217 : Upper (D 6) (R 6) [34,129,96,5,258] 13 := by
  apply FastRouting.sound _ _ [34,129,96,5,258] 13 (by decide) (choices 1) [4,8,16,64] r37217 c37217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22207
  · exact u22208
  · exact u22209
  · exact u22210

def r37218 : Route 9 := (fun mask => (mask,id))

def c37218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37218 : Upper (D 6) (R 6) [34,129,96,5,260] 13 := by
  apply FastRouting.sound _ _ [34,129,96,5,260] 13 (by decide) (choices 1) [2,8,16,64] r37218 c37218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22211
  · exact u22212
  · exact u22213
  · exact u22214

def r37219 : Route 9 := (fun mask => (mask,id))

def c37219 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37219 : Upper (D 6) (R 6) [34,129,96,5,264] 13 := by
  apply FastRouting.sound _ _ [34,129,96,5,264] 13 (by decide) (choices 1) [2,4,16,64] r37219 c37219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22215
  · exact u22216
  · exact u22217
  · exact u22218

def r37220 : Route 9 := (fun mask => (mask,id))

def c37220 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37220 : Upper (D 6) (R 6) [34,129,96,5,320] 13 := by
  apply FastRouting.sound _ _ [34,129,96,5,320] 13 (by decide) (choices 1) [2,4,8,16] r37220 c37220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22219
  · exact u22220
  · exact u22221
  · exact u22222

def r37221 : Route 9 := (fun mask => (mask,id))

def c37221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37221 : Upper (D 6) (R 6) [34,129,96,6,9] 13 := by
  apply FastRouting.sound _ _ [34,129,96,6,9] 13 (by decide) (choices 1) [4,16,64,256] r37221 c37221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22223
  · exact u22224
  · exact u22225
  · exact u22226

def b37222 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 100 14 28 369 337 465 337), lower := (rows 35 131 100 14 28 32 64 128 256), losses := [] }

theorem u37222 : Upper (D 6) (R 6) [34,129,96,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37223 : Route 9 := (fun mask => (mask,id))

def c37223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37223 : Upper (D 6) (R 6) [34,129,96,6,65] 13 := by
  apply FastRouting.sound _ _ [34,129,96,6,65] 13 (by decide) (choices 1) [4,8,16,256] r37223 c37223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22227
  · exact u22228
  · exact u22229
  · exact u22230

def b37224 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 100 14 84 313 345 409 281), lower := (rows 35 131 100 14 84 32 64 128 256), losses := [] }

theorem u37224 : Upper (D 6) (R 6) [34,129,96,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37225 : Route 9 := (fun mask => (mask,id))

def c37225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37225 : Upper (D 6) (R 6) [34,129,96,6,72] 13 := by
  apply FastRouting.sound _ _ [34,129,96,6,72] 13 (by decide) (choices 1) [1,4,16,256] r37225 c37225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22231
  · exact u22232
  · exact u22233
  · exact u22234

def r37226 : Route 9 := (fun mask => (mask,id))

def c37226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37226 : Upper (D 6) (R 6) [34,129,96,6,257] 13 := by
  apply FastRouting.sound _ _ [34,129,96,6,257] 13 (by decide) (choices 1) [4,8,16,64] r37226 c37226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22235
  · exact u22236
  · exact u22237
  · exact u22238

def r37227 : Route 9 := (fun mask => (mask,id))

def c37227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37227 : Upper (D 6) (R 6) [34,129,96,6,260] 13 := by
  apply FastRouting.sound _ _ [34,129,96,6,260] 13 (by decide) (choices 1) [1,8,16,64] r37227 c37227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22239
  · exact u22240
  · exact u22241
  · exact u22242

def r37228 : Route 9 := (fun mask => (mask,id))

def c37228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37228 : Upper (D 6) (R 6) [34,129,96,6,264] 13 := by
  apply FastRouting.sound _ _ [34,129,96,6,264] 13 (by decide) (choices 1) [1,4,16,64] r37228 c37228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22243
  · exact u22244
  · exact u22245
  · exact u22246

def r37229 : Route 9 := (fun mask => (mask,id))

def c37229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37229 : Upper (D 6) (R 6) [34,129,96,6,320] 13 := by
  apply FastRouting.sound _ _ [34,129,96,6,320] 13 (by decide) (choices 1) [1,4,8,16] r37229 c37229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22247
  · exact u22248
  · exact u22249
  · exact u22250

def b37230 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 131 100 25 26 356 324 452 324), lower := (rows 35 131 100 25 26 32 64 128 256), losses := [] }

theorem u37230 : Upper (D 6) (R 6) [34,129,96,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37231 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 324, targets := 1 }], pairs := [(1,5),(2,0),(4,0)], upper := (rows 35 131 100 25 28 358 326 454 326), lower := (rows 35 131 100 25 28 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 15 8 24 35 67 131 259), good := (rows 486 486 100 508 28 32 64 128 256) },{ target := 5, region := (rows 1 10 4 8 16 0 80 144 272), good := (rows 3 131 68 475 478 0 64 128 256) }] }

theorem u37231 : Upper (D 6) (R 6) [34,129,96,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37232 : Route 9 := (fun mask => (mask,id))

def c37232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37232 : Upper (D 6) (R 6) [34,129,96,17,66] 13 := by
  apply FastRouting.sound _ _ [34,129,96,17,66] 13 (by decide) (choices 1) [4,8,256] r37232 c37232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22251
  · exact u22252
  · exact u22253

def b37233 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 100 25 84 302 334 398 270), lower := (rows 35 131 100 25 84 32 64 128 256), losses := [] }

theorem u37233 : Upper (D 6) (R 6) [34,129,96,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37234 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 0, region := 324, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 100 25 88 294 326 390 262), lower := (rows 35 131 100 25 88 32 64 128 256), losses := [] }

theorem u37234 : Upper (D 6) (R 6) [34,129,96,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37235 : Route 9 := (fun mask => (mask,id))

def c37235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37235 : Upper (D 6) (R 6) [34,129,96,17,258] 13 := by
  apply FastRouting.sound _ _ [34,129,96,17,258] 13 (by decide) (choices 1) [4,8,64] r37235 c37235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22254
  · exact u22255
  · exact u22256

def r37236 : Route 9 := (fun mask => (mask,id))

def c37236 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37236 : Upper (D 6) (R 6) [34,129,96,17,260] 13 := by
  apply FastRouting.sound _ _ [34,129,96,17,260] 13 (by decide) (choices 1) [2,4,8,64] r37236 c37236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22257
  · exact u22258
  · exact u22259
  · exact u22260

def r37237 : Route 9 := (fun mask => (mask,id))

def c37237 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37237 : Upper (D 6) (R 6) [34,129,96,17,264] 13 := by
  apply FastRouting.sound _ _ [34,129,96,17,264] 13 (by decide) (choices 1) [2,4,64] r37237 c37237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22261
  · exact u22262
  · exact u22263

def r37238 : Route 9 := (fun mask => (mask,id))

def c37238 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37238 : Upper (D 6) (R 6) [34,129,96,17,320] 13 := by
  apply FastRouting.sound _ _ [34,129,96,17,320] 13 (by decide) (choices 1) [2,4,8] r37238 c37238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22264
  · exact u22265
  · exact u22266

def r37239 : Route 9 := (fun mask => (mask,id))

def c37239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37239 : Upper (D 6) (R 6) [34,129,96,18,12] 13 := by
  apply FastRouting.sound _ _ [34,129,96,18,12] 13 (by decide) (choices 1) [1,4,64,256] r37239 c37239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22267
  · exact u22268
  · exact u22269
  · exact u22270

def r37240 : Route 9 := (fun mask => (mask,id))

def c37240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37240 : Upper (D 6) (R 6) [34,129,96,18,65] 13 := by
  apply FastRouting.sound _ _ [34,129,96,18,65] 13 (by decide) (choices 1) [4,8,256] r37240 c37240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22271
  · exact u22272
  · exact u22273

def b37241 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 100 26 84 301 333 397 269), lower := (rows 35 131 100 26 84 32 64 128 256), losses := [] }

theorem u37241 : Upper (D 6) (R 6) [34,129,96,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37242 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 35 131 100 26 88 293 325 389 261), lower := (rows 35 131 100 26 88 32 64 128 256), losses := [] }

theorem u37242 : Upper (D 6) (R 6) [34,129,96,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37243 : Route 9 := (fun mask => (mask,id))

def c37243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37243 : Upper (D 6) (R 6) [34,129,96,18,257] 13 := by
  apply FastRouting.sound _ _ [34,129,96,18,257] 13 (by decide) (choices 1) [4,8,64] r37243 c37243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22274
  · exact u22275
  · exact u22276

def r37244 : Route 9 := (fun mask => (mask,id))

def c37244 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37244 : Upper (D 6) (R 6) [34,129,96,18,260] 13 := by
  apply FastRouting.sound _ _ [34,129,96,18,260] 13 (by decide) (choices 1) [1,4,8,64] r37244 c37244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22277
  · exact u22278
  · exact u22279
  · exact u22280

def r37245 : Route 9 := (fun mask => (mask,id))

def c37245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37245 : Upper (D 6) (R 6) [34,129,96,18,264] 13 := by
  apply FastRouting.sound _ _ [34,129,96,18,264] 13 (by decide) (choices 1) [1,4,64] r37245 c37245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22281
  · exact u22282
  · exact u22283

def r37246 : Route 9 := (fun mask => (mask,id))

def c37246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37246 : Upper (D 6) (R 6) [34,129,96,18,320] 13 := by
  apply FastRouting.sound _ _ [34,129,96,18,320] 13 (by decide) (choices 1) [1,4,8] r37246 c37246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22284
  · exact u22285
  · exact u22286

def b37247 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 100 28 28 355 323 451 323), lower := (rows 35 131 100 28 28 32 64 128 256), losses := [] }

theorem u37247 : Upper (D 6) (R 6) [34,129,96,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37248 : Route 9 := (fun mask => (mask,id))

def c37248 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37248 : Upper (D 6) (R 6) [34,129,96,20,65] 13 := by
  apply FastRouting.sound _ _ [34,129,96,20,65] 13 (by decide) (choices 1) [2,4,8,256] r37248 c37248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22287
  · exact u22288
  · exact u22289
  · exact u22290

def r37249 : Route 9 := (fun mask => (mask,id))

def c37249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37249 : Upper (D 6) (R 6) [34,129,96,20,66] 13 := by
  apply FastRouting.sound _ _ [34,129,96,20,66] 13 (by decide) (choices 1) [1,4,8,256] r37249 c37249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22291
  · exact u22292
  · exact u22293
  · exact u22294

def b37250 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 100 28 84 299 331 395 267), lower := (rows 35 131 100 28 84 32 64 128 256), losses := [] }

theorem u37250 : Upper (D 6) (R 6) [34,129,96,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37251 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 100 28 88 295 327 391 263), lower := (rows 35 131 100 28 88 32 64 128 256), losses := [] }

theorem u37251 : Upper (D 6) (R 6) [34,129,96,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37252 : Route 9 := (fun mask => (mask,id))

def c37252 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37252 : Upper (D 6) (R 6) [34,129,96,20,257] 13 := by
  apply FastRouting.sound _ _ [34,129,96,20,257] 13 (by decide) (choices 1) [2,4,8,64] r37252 c37252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22295
  · exact u22296
  · exact u22297
  · exact u22298

def r37253 : Route 9 := (fun mask => (mask,id))

def c37253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37253 : Upper (D 6) (R 6) [34,129,96,20,258] 13 := by
  apply FastRouting.sound _ _ [34,129,96,20,258] 13 (by decide) (choices 1) [1,4,8,64] r37253 c37253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22299
  · exact u22300
  · exact u22301
  · exact u22302

def b37254 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 100 28 276 107 75 203 331), lower := (rows 35 131 100 28 276 32 64 128 256), losses := [] }

theorem u37254 : Upper (D 6) (R 6) [34,129,96,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37255 : Route 9 := (fun mask => (mask,id))

def c37255 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37255 : Upper (D 6) (R 6) [34,129,96,20,264] 13 := by
  apply FastRouting.sound _ _ [34,129,96,20,264] 13 (by decide) (choices 1) [1,2,4,64] r37255 c37255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22303
  · exact u22304
  · exact u22305
  · exact u22306

def r37256 : Route 9 := (fun mask => (mask,id))

def c37256 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37256 : Upper (D 6) (R 6) [34,129,96,20,320] 13 := by
  apply FastRouting.sound _ _ [34,129,96,20,320] 13 (by decide) (choices 1) [1,2,4,8] r37256 c37256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22307
  · exact u22308
  · exact u22309
  · exact u22310

def r37257 : Route 9 := (fun mask => (mask,id))

def c37257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37257 : Upper (D 6) (R 6) [34,129,96,65,258] 13 := by
  apply FastRouting.sound _ _ [34,129,96,65,258] 13 (by decide) (choices 1) [4,8,16] r37257 c37257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22311
  · exact u22312
  · exact u22313

def r37258 : Route 9 := (fun mask => (mask,id))

def c37258 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37258 : Upper (D 6) (R 6) [34,129,96,65,260] 13 := by
  apply FastRouting.sound _ _ [34,129,96,65,260] 13 (by decide) (choices 1) [2,4,8,16] r37258 c37258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22314
  · exact u22315
  · exact u22316
  · exact u22317

def r37259 : Route 9 := (fun mask => (mask,id))

def c37259 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37259 : Upper (D 6) (R 6) [34,129,96,65,264] 13 := by
  apply FastRouting.sound _ _ [34,129,96,65,264] 13 (by decide) (choices 1) [2,4,16] r37259 c37259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22318
  · exact u22319
  · exact u22320

#print axioms u37259
end Delivery.IrregularNine14.P06
