import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0338
import IrregularNine14P06C0339
import IrregularNine14P06C0340

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36060 : Route 9 := (fun mask => (mask,id))

def c36060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u36060 : Upper (D 6) (R 6) [34,68,130,5,40] 13 := by
  apply FastRouting.sound _ _ [34,68,130,5,40] 13 (by decide) (choices 1) [1,16,64,256] r36060 c36060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20295
  · exact u20296
  · exact u20297
  · exact u20298

def r36061 : Route 9 := (fun mask => (mask,id))

def c36061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36061 : Upper (D 6) (R 6) [34,68,130,5,65] 13 := by
  apply FastRouting.sound _ _ [34,68,130,5,65] 13 (by decide) (choices 1) [8,16,256] r36061 c36061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20299
  · exact u20300
  · exact u20301

def r36062 : Route 9 := (fun mask => (mask,id))

def c36062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36062 : Upper (D 6) (R 6) [34,68,130,5,72] 13 := by
  apply FastRouting.sound _ _ [34,68,130,5,72] 13 (by decide) (choices 1) [1,16,256] r36062 c36062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20302
  · exact u20303
  · exact u20304

def r36063 : Route 9 := (fun mask => (mask,id))

def c36063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36063 : Upper (D 6) (R 6) [34,68,130,5,96] 13 := by
  apply FastRouting.sound _ _ [34,68,130,5,96] 13 (by decide) (choices 1) [1,8,16,256] r36063 c36063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20305
  · exact u20306
  · exact u20307
  · exact u20308

def r36064 : Route 9 := (fun mask => (mask,id))

def c36064 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36064 : Upper (D 6) (R 6) [34,68,130,5,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,5,257] 13 (by decide) (choices 1) [8,16,64] r36064 c36064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20309
  · exact u20310
  · exact u20311

def r36065 : Route 9 := (fun mask => (mask,id))

def c36065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36065 : Upper (D 6) (R 6) [34,68,130,5,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,5,264] 13 (by decide) (choices 1) [1,16,64] r36065 c36065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20312
  · exact u20313
  · exact u20314

def r36066 : Route 9 := (fun mask => (mask,id))

def c36066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36066 : Upper (D 6) (R 6) [34,68,130,5,288] 13 := by
  apply FastRouting.sound _ _ [34,68,130,5,288] 13 (by decide) (choices 1) [1,8,16,64] r36066 c36066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20315
  · exact u20316
  · exact u20317
  · exact u20318

def r36067 : Route 9 := (fun mask => (mask,id))

def c36067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36067 : Upper (D 6) (R 6) [34,68,130,5,320] 13 := by
  apply FastRouting.sound _ _ [34,68,130,5,320] 13 (by decide) (choices 1) [1,8,16] r36067 c36067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20319
  · exact u20320
  · exact u20321

def b36068 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 134 25 25 356 356 484 356), lower := (rows 35 70 134 25 25 32 64 128 256), losses := [] }

theorem u36068 : Upper (D 6) (R 6) [34,68,130,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36069 : Route 9 := (fun mask => (mask,id))

def c36069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36069 : Upper (D 6) (R 6) [34,68,130,17,12] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,12] 13 (by decide) (choices 1) [1,64,256] r36069 c36069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20322
  · exact u20323
  · exact u20324

def b36070 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 134 25 49 364 332 460 332), lower := (rows 35 70 134 25 49 32 64 128 256), losses := [] }

theorem u36070 : Upper (D 6) (R 6) [34,68,130,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36071 : Route 9 := (fun mask => (mask,id))

def c36071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36071 : Upper (D 6) (R 6) [34,68,130,17,36] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,36] 13 (by decide) (choices 1) [1,8,64,256] r36071 c36071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20325
  · exact u20326
  · exact u20327
  · exact u20328

def b36072 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 134 25 56 357 325 453 325), lower := (rows 35 70 134 25 56 32 64 128 256), losses := [] }

theorem u36072 : Upper (D 6) (R 6) [34,68,130,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36073 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 134 25 81 300 364 428 300), lower := (rows 35 70 134 25 81 32 64 128 256), losses := [] }

theorem u36073 : Upper (D 6) (R 6) [34,68,130,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36074 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 134 25 84 297 361 425 297), lower := (rows 35 70 134 25 84 32 64 128 256), losses := [] }

theorem u36074 : Upper (D 6) (R 6) [34,68,130,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36075 : Route 9 := (fun mask => (mask,id))

def c36075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36075 : Upper (D 6) (R 6) [34,68,130,17,72] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,72] 13 (by decide) (choices 1) [1,4,256] r36075 c36075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20329
  · exact u20330
  · exact u20331

def r36076 : Route 9 := (fun mask => (mask,id))

def c36076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36076 : Upper (D 6) (R 6) [34,68,130,17,96] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,96] 13 (by decide) (choices 1) [1,4,8,256] r36076 c36076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20332
  · exact u20333
  · exact u20334
  · exact u20335

def b36077 : PairBound 9 := { available := 108, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 134 25 273 108 108 236 364), lower := (rows 35 70 134 25 273 32 64 128 256), losses := [] }

theorem u36077 : Upper (D 6) (R 6) [34,68,130,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36078 : Route 9 := (fun mask => (mask,id))

def c36078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36078 : Upper (D 6) (R 6) [34,68,130,17,260] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,260] 13 (by decide) (choices 1) [1,8,64] r36078 c36078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20336
  · exact u20337
  · exact u20338

def r36079 : Route 9 := (fun mask => (mask,id))

def c36079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36079 : Upper (D 6) (R 6) [34,68,130,17,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,264] 13 (by decide) (choices 1) [1,4,64] r36079 c36079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20339
  · exact u20340
  · exact u20341

def r36080 : Route 9 := (fun mask => (mask,id))

def c36080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36080 : Upper (D 6) (R 6) [34,68,130,17,288] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,288] 13 (by decide) (choices 1) [1,4,8,64] r36080 c36080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20342
  · exact u20343
  · exact u20344
  · exact u20345

def r36081 : Route 9 := (fun mask => (mask,id))

def c36081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36081 : Upper (D 6) (R 6) [34,68,130,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,320] 13 (by decide) (choices 1) [1,4,8] r36081 c36081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20346
  · exact u20347
  · exact u20348

def b36082 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 134 28 49 361 329 457 329), lower := (rows 35 70 134 28 49 32 64 128 256), losses := [] }

theorem u36082 : Upper (D 6) (R 6) [34,68,130,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36083 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 70 134 28 56 353 321 449 321), lower := (rows 35 70 134 28 56 32 64 128 256), losses := [] }

theorem u36083 : Upper (D 6) (R 6) [34,68,130,20,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36084 : Route 9 := (fun mask => (mask,id))

def c36084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36084 : Upper (D 6) (R 6) [34,68,130,20,65] 13 := by
  apply FastRouting.sound _ _ [34,68,130,20,65] 13 (by decide) (choices 1) [1,8,256] r36084 c36084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20349
  · exact u20350
  · exact u20351

def b36085 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 134 28 88 289 353 417 289), lower := (rows 35 70 134 28 88 32 64 128 256), losses := [] }

theorem u36085 : Upper (D 6) (R 6) [34,68,130,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36086 : Route 9 := (fun mask => (mask,id))

def c36086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36086 : Upper (D 6) (R 6) [34,68,130,20,96] 13 := by
  apply FastRouting.sound _ _ [34,68,130,20,96] 13 (by decide) (choices 1) [1,8,256] r36086 c36086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20352
  · exact u20353
  · exact u20354

def r36087 : Route 9 := (fun mask => (mask,id))

def c36087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36087 : Upper (D 6) (R 6) [34,68,130,20,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,20,257] 13 (by decide) (choices 1) [1,8,64] r36087 c36087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20355
  · exact u20356
  · exact u20357

def r36088 : Route 9 := (fun mask => (mask,id))

def c36088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36088 : Upper (D 6) (R 6) [34,68,130,20,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,20,264] 13 (by decide) (choices 1) [1,64] r36088 c36088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20358
  · exact u20359

def r36089 : Route 9 := (fun mask => (mask,id))

def c36089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36089 : Upper (D 6) (R 6) [34,68,130,20,288] 13 := by
  apply FastRouting.sound _ _ [34,68,130,20,288] 13 (by decide) (choices 1) [1,8,64] r36089 c36089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20360
  · exact u20361
  · exact u20362

def r36090 : Route 9 := (fun mask => (mask,id))

def c36090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36090 : Upper (D 6) (R 6) [34,68,130,20,320] 13 := by
  apply FastRouting.sound _ _ [34,68,130,20,320] 13 (by decide) (choices 1) [1,8] r36090 c36090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20363
  · exact u20364

def b36091 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 134 41 81 316 348 412 284), lower := (rows 35 70 134 41 81 32 64 128 256), losses := [] }

theorem u36091 : Upper (D 6) (R 6) [34,68,130,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36092 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 134 41 88 309 341 405 277), lower := (rows 35 70 134 41 88 32 64 128 256), losses := [] }

theorem u36092 : Upper (D 6) (R 6) [34,68,130,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36093 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 134 41 273 124 92 220 348), lower := (rows 35 70 134 41 273 32 64 128 256), losses := [] }

theorem u36093 : Upper (D 6) (R 6) [34,68,130,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36094 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 134 41 276 121 89 217 345), lower := (rows 35 70 134 41 276 32 64 128 256), losses := [] }

theorem u36094 : Upper (D 6) (R 6) [34,68,130,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36095 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 134 41 280 117 85 213 341), lower := (rows 35 70 134 41 280 32 64 128 256), losses := [] }

theorem u36095 : Upper (D 6) (R 6) [34,68,130,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36096 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 134 41 336 61 93 157 285), lower := (rows 35 70 134 41 336 32 64 128 256), losses := [] }

theorem u36096 : Upper (D 6) (R 6) [34,68,130,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36097 : Route 9 := (fun mask => (mask,id))

def c36097 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36097 : Upper (D 6) (R 6) [34,68,130,36,65] 13 := by
  apply FastRouting.sound _ _ [34,68,130,36,65] 13 (by decide) (choices 1) [1,8,16,256] r36097 c36097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20365
  · exact u20366
  · exact u20367
  · exact u20368

def r36098 : Route 9 := (fun mask => (mask,id))

def c36098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36098 : Upper (D 6) (R 6) [34,68,130,36,72] 13 := by
  apply FastRouting.sound _ _ [34,68,130,36,72] 13 (by decide) (choices 1) [1,16,256] r36098 c36098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20369
  · exact u20370
  · exact u20371

def r36099 : Route 9 := (fun mask => (mask,id))

def c36099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36099 : Upper (D 6) (R 6) [34,68,130,36,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,36,257] 13 (by decide) (choices 1) [1,8,16,64] r36099 c36099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20372
  · exact u20373
  · exact u20374
  · exact u20375

def r36100 : Route 9 := (fun mask => (mask,id))

def c36100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36100 : Upper (D 6) (R 6) [34,68,130,36,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,36,264] 13 (by decide) (choices 1) [1,16,64] r36100 c36100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20376
  · exact u20377
  · exact u20378

def r36101 : Route 9 := (fun mask => (mask,id))

def c36101 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36101 : Upper (D 6) (R 6) [34,68,130,36,320] 13 := by
  apply FastRouting.sound _ _ [34,68,130,36,320] 13 (by decide) (choices 1) [1,8,16] r36101 c36101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20379
  · exact u20380
  · exact u20381

def r36102 : Route 9 := (fun mask => (mask,id))

def c36102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36102 : Upper (D 6) (R 6) [34,68,130,48,65] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,65] 13 (by decide) (choices 1) [1,4,8,256] r36102 c36102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20382
  · exact u20383
  · exact u20384
  · exact u20385

def b36103 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 134 56 84 297 329 393 265), lower := (rows 35 70 134 56 84 32 64 128 256), losses := [] }

theorem u36103 : Upper (D 6) (R 6) [34,68,130,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36104 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 70 134 56 88 293 325 389 261), lower := (rows 35 70 134 56 88 32 64 128 256), losses := [] }

theorem u36104 : Upper (D 6) (R 6) [34,68,130,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36105 : Route 9 := (fun mask => (mask,id))

def c36105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36105 : Upper (D 6) (R 6) [34,68,130,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,257] 13 (by decide) (choices 1) [1,4,8,64] r36105 c36105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20386
  · exact u20387
  · exact u20388
  · exact u20389

def r36106 : Route 9 := (fun mask => (mask,id))

def c36106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36106 : Upper (D 6) (R 6) [34,68,130,48,260] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,260] 13 (by decide) (choices 1) [1,8,64] r36106 c36106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20390
  · exact u20391
  · exact u20392

def r36107 : Route 9 := (fun mask => (mask,id))

def c36107 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36107 : Upper (D 6) (R 6) [34,68,130,48,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,264] 13 (by decide) (choices 1) [1,4,64] r36107 c36107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20393
  · exact u20394
  · exact u20395

def r36108 : Route 9 := (fun mask => (mask,id))

def c36108 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36108 : Upper (D 6) (R 6) [34,68,130,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,320] 13 (by decide) (choices 1) [1,4,8] r36108 c36108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20396
  · exact u20397
  · exact u20398

def r36109 : Route 9 := (fun mask => (mask,id))

def c36109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36109 : Upper (D 6) (R 6) [34,68,130,65,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65,257] 13 (by decide) (choices 1) [4,8,16] r36109 c36109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20399
  · exact u20400
  · exact u20401

def r36110 : Route 9 := (fun mask => (mask,id))

def c36110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36110 : Upper (D 6) (R 6) [34,68,130,65,260] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65,260] 13 (by decide) (choices 1) [1,8,16] r36110 c36110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20402
  · exact u20403
  · exact u20404

def r36111 : Route 9 := (fun mask => (mask,id))

def c36111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36111 : Upper (D 6) (R 6) [34,68,130,65,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65,264] 13 (by decide) (choices 1) [1,4,16] r36111 c36111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20405
  · exact u20406
  · exact u20407

def r36112 : Route 9 := (fun mask => (mask,id))

def c36112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36112 : Upper (D 6) (R 6) [34,68,130,65,288] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65,288] 13 (by decide) (choices 1) [1,4,8,16] r36112 c36112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20408
  · exact u20409
  · exact u20410
  · exact u20411

def b36113 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 134 76 273 57 121 185 313), lower := (rows 35 70 134 76 273 32 64 128 256), losses := [] }

theorem u36113 : Upper (D 6) (R 6) [34,68,130,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36114 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 134 76 280 49 113 177 305), lower := (rows 35 70 134 76 280 32 64 128 256), losses := [] }

theorem u36114 : Upper (D 6) (R 6) [34,68,130,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36115 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 134 76 304 57 89 153 281), lower := (rows 35 70 134 76 304 32 64 128 256), losses := [] }

theorem u36115 : Upper (D 6) (R 6) [34,68,130,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36116 : Route 9 := (fun mask => (mask,id))

def c36116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36116 : Upper (D 6) (R 6) [34,68,130,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,257] 13 (by decide) (choices 1) [1,4,8] r36116 c36116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20412
  · exact u20413
  · exact u20414

def r36117 : Route 9 := (fun mask => (mask,id))

def c36117 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36117 : Upper (D 6) (R 6) [34,68,130,80,260] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,260] 13 (by decide) (choices 1) [1,8] r36117 c36117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20415
  · exact u20416

def r36118 : Route 9 := (fun mask => (mask,id))

def c36118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36118 : Upper (D 6) (R 6) [34,68,130,80,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,264] 13 (by decide) (choices 1) [1,4] r36118 c36118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20417
  · exact u20418

def r36119 : Route 9 := (fun mask => (mask,id))

def c36119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36119 : Upper (D 6) (R 6) [34,68,130,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,288] 13 (by decide) (choices 1) [1,4,8] r36119 c36119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20419
  · exact u20420
  · exact u20421

#print axioms u36119
end Delivery.IrregularNine14.P06
