import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0372
import IrregularNine14P06C0373
import IrregularNine14P06C0374

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37260 : Route 9 := (fun mask => (mask,id))

def c37260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37260 : Upper (D 6) (R 6) [34,129,96,66,257] 13 := by
  apply FastRouting.sound _ _ [34,129,96,66,257] 13 (by decide) (choices 1) [4,8,16] r37260 c37260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22321
  · exact u22322
  · exact u22323

def r37261 : Route 9 := (fun mask => (mask,id))

def c37261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37261 : Upper (D 6) (R 6) [34,129,96,66,260] 13 := by
  apply FastRouting.sound _ _ [34,129,96,66,260] 13 (by decide) (choices 1) [1,4,8,16] r37261 c37261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22324
  · exact u22325
  · exact u22326
  · exact u22327

def r37262 : Route 9 := (fun mask => (mask,id))

def c37262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37262 : Upper (D 6) (R 6) [34,129,96,66,264] 13 := by
  apply FastRouting.sound _ _ [34,129,96,66,264] 13 (by decide) (choices 1) [1,4,16] r37262 c37262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22328
  · exact u22329
  · exact u22330

def b37263 : PairBound 9 := { available := 30, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 100 76 273 62 94 158 286), lower := (rows 35 131 100 76 273 32 64 128 256), losses := [] }

theorem u37263 : Upper (D 6) (R 6) [34,129,96,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37264 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 100 76 274 61 93 157 285), lower := (rows 35 131 100 76 274 32 64 128 256), losses := [] }

theorem u37264 : Upper (D 6) (R 6) [34,129,96,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37265 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 100 76 276 59 91 155 283), lower := (rows 35 131 100 76 276 32 64 128 256), losses := [] }

theorem u37265 : Upper (D 6) (R 6) [34,129,96,68,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37266 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 100 76 280 55 87 151 279), lower := (rows 35 131 100 76 280 32 64 128 256), losses := [] }

theorem u37266 : Upper (D 6) (R 6) [34,129,96,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37267 : Route 9 := (fun mask => (mask,id))

def c37267 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37267 : Upper (D 6) (R 6) [34,129,96,80,257] 13 := by
  apply FastRouting.sound _ _ [34,129,96,80,257] 13 (by decide) (choices 1) [2,4,8] r37267 c37267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22331
  · exact u22332
  · exact u22333

def r37268 : Route 9 := (fun mask => (mask,id))

def c37268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37268 : Upper (D 6) (R 6) [34,129,96,80,258] 13 := by
  apply FastRouting.sound _ _ [34,129,96,80,258] 13 (by decide) (choices 1) [1,4,8] r37268 c37268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22334
  · exact u22335
  · exact u22336

def r37269 : Route 9 := (fun mask => (mask,id))

def c37269 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37269 : Upper (D 6) (R 6) [34,129,96,80,260] 13 := by
  apply FastRouting.sound _ _ [34,129,96,80,260] 13 (by decide) (choices 1) [1,2,4,8] r37269 c37269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22337
  · exact u22338
  · exact u22339
  · exact u22340

def r37270 : Route 9 := (fun mask => (mask,id))

def c37270 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37270 : Upper (D 6) (R 6) [34,129,96,80,264] 13 := by
  apply FastRouting.sound _ _ [34,129,96,80,264] 13 (by decide) (choices 1) [1,2,4] r37270 c37270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22341
  · exact u22342
  · exact u22343

def b37271 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 3 },{ cop := 3, region := 16, targets := 32 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 261 14 28 112 112 240 368), lower := (rows 35 131 261 14 28 32 64 128 256), losses := [] }

theorem u37271 : Upper (D 6) (R 6) [34,129,257,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37272 : Route 9 := (fun mask => (mask,id))

def c37272 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37272 : Upper (D 6) (R 6) [34,129,257,6,36] 13 := by
  apply FastRouting.sound _ _ [34,129,257,6,36] 13 (by decide) (choices 1) [8,16,64] r37272 c37272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22344
  · exact u22345
  · exact u22346

def r37273 : Route 9 := (fun mask => (mask,id))

def c37273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37273 : Upper (D 6) (R 6) [34,129,257,6,40] 13 := by
  apply FastRouting.sound _ _ [34,129,257,6,40] 13 (by decide) (choices 1) [4,16,64] r37273 c37273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22347
  · exact u22348
  · exact u22349

def r37274 : Route 9 := (fun mask => (mask,id))

def c37274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37274 : Upper (D 6) (R 6) [34,129,257,6,68] 13 := by
  apply FastRouting.sound _ _ [34,129,257,6,68] 13 (by decide) (choices 1) [8,16,64] r37274 c37274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22350
  · exact u22351
  · exact u22352

def r37275 : Route 9 := (fun mask => (mask,id))

def c37275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37275 : Upper (D 6) (R 6) [34,129,257,6,72] 13 := by
  apply FastRouting.sound _ _ [34,129,257,6,72] 13 (by decide) (choices 1) [4,16,64] r37275 c37275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22353
  · exact u22354
  · exact u22355

def r37276 : Route 9 := (fun mask => (mask,id))

def c37276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37276 : Upper (D 6) (R 6) [34,129,257,6,96] 13 := by
  apply FastRouting.sound _ _ [34,129,257,6,96] 13 (by decide) (choices 1) [4,8,16,64] r37276 c37276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22356
  · exact u22357
  · exact u22358
  · exact u22359

def r37277 : Route 9 := (fun mask => (mask,id))

def c37277 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37277 : Upper (D 6) (R 6) [34,129,257,18,12] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18,12] 13 (by decide) (choices 1) [4,64] r37277 c37277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22360
  · exact u22361

def r37278 : Route 9 := (fun mask => (mask,id))

def c37278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37278 : Upper (D 6) (R 6) [34,129,257,18,36] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18,36] 13 (by decide) (choices 1) [4,8,64] r37278 c37278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22362
  · exact u22363
  · exact u22364

def b37279 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 131 261 26 56 100 68 196 324), lower := (rows 35 131 261 26 56 32 64 128 256), losses := [] }

theorem u37279 : Upper (D 6) (R 6) [34,129,257,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37280 : Route 9 := (fun mask => (mask,id))

def c37280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37280 : Upper (D 6) (R 6) [34,129,257,18,68] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18,68] 13 (by decide) (choices 1) [4,8,64] r37280 c37280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22365
  · exact u22366
  · exact u22367

def r37281 : Route 9 := (fun mask => (mask,id))

def c37281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37281 : Upper (D 6) (R 6) [34,129,257,18,72] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18,72] 13 (by decide) (choices 1) [4,64] r37281 c37281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22368
  · exact u22369

def r37282 : Route 9 := (fun mask => (mask,id))

def c37282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37282 : Upper (D 6) (R 6) [34,129,257,18,96] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18,96] 13 (by decide) (choices 1) [4,8,64] r37282 c37282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22370
  · exact u22371
  · exact u22372

def b37283 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 261 28 28 98 98 226 354), lower := (rows 35 131 261 28 28 32 64 128 256), losses := [] }

theorem u37283 : Upper (D 6) (R 6) [34,129,257,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37284 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 261 28 50 108 76 204 332), lower := (rows 35 131 261 28 50 32 64 128 256), losses := [] }

theorem u37284 : Upper (D 6) (R 6) [34,129,257,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37285 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 261 28 52 106 74 202 330), lower := (rows 35 131 261 28 52 32 64 128 256), losses := [] }

theorem u37285 : Upper (D 6) (R 6) [34,129,257,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37286 : Route 9 := (fun mask => (mask,id))

def c37286 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37286 : Upper (D 6) (R 6) [34,129,257,20,40] 13 := by
  apply FastRouting.sound _ _ [34,129,257,20,40] 13 (by decide) (choices 1) [2,4,64] r37286 c37286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22373
  · exact u22374
  · exact u22375

def r37287 : Route 9 := (fun mask => (mask,id))

def c37287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37287 : Upper (D 6) (R 6) [34,129,257,20,66] 13 := by
  apply FastRouting.sound _ _ [34,129,257,20,66] 13 (by decide) (choices 1) [4,8,64] r37287 c37287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22376
  · exact u22377
  · exact u22378

def b37288 : PairBound 9 := { available := 106, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 261 28 84 106 106 234 362), lower := (rows 35 131 261 28 84 32 64 128 256), losses := [] }

theorem u37288 : Upper (D 6) (R 6) [34,129,257,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37289 : Route 9 := (fun mask => (mask,id))

def c37289 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37289 : Upper (D 6) (R 6) [34,129,257,20,72] 13 := by
  apply FastRouting.sound _ _ [34,129,257,20,72] 13 (by decide) (choices 1) [2,4,64] r37289 c37289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22379
  · exact u22380
  · exact u22381

def r37290 : Route 9 := (fun mask => (mask,id))

def c37290 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37290 : Upper (D 6) (R 6) [34,129,257,20,96] 13 := by
  apply FastRouting.sound _ _ [34,129,257,20,96] 13 (by decide) (choices 1) [2,4,8,64] r37290 c37290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22382
  · exact u22383
  · exact u22384
  · exact u22385

def b37291 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 131 261 42 84 124 92 220 348), lower := (rows 35 131 261 42 84 32 64 128 256), losses := [] }

theorem u37291 : Upper (D 6) (R 6) [34,129,257,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37292 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 131 261 42 88 116 84 212 340), lower := (rows 35 131 261 42 88 32 64 128 256), losses := [] }

theorem u37292 : Upper (D 6) (R 6) [34,129,257,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37293 : Route 9 := (fun mask => (mask,id))

def c37293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37293 : Upper (D 6) (R 6) [34,129,257,36,66] 13 := by
  apply FastRouting.sound _ _ [34,129,257,36,66] 13 (by decide) (choices 1) [4,8,16,64] r37293 c37293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22386
  · exact u22387
  · exact u22388
  · exact u22389

def r37294 : Route 9 := (fun mask => (mask,id))

def c37294 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37294 : Upper (D 6) (R 6) [34,129,257,36,68] 13 := by
  apply FastRouting.sound _ _ [34,129,257,36,68] 13 (by decide) (choices 1) [2,8,16,64] r37294 c37294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22390
  · exact u22391
  · exact u22392
  · exact u22393

def r37295 : Route 9 := (fun mask => (mask,id))

def c37295 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37295 : Upper (D 6) (R 6) [34,129,257,36,72] 13 := by
  apply FastRouting.sound _ _ [34,129,257,36,72] 13 (by decide) (choices 1) [2,4,16,64] r37295 c37295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22394
  · exact u22395
  · exact u22396
  · exact u22397

def r37296 : Route 9 := (fun mask => (mask,id))

def c37296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37296 : Upper (D 6) (R 6) [34,129,257,48,66] 13 := by
  apply FastRouting.sound _ _ [34,129,257,48,66] 13 (by decide) (choices 1) [4,8,64] r37296 c37296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22398
  · exact u22399
  · exact u22400

def r37297 : Route 9 := (fun mask => (mask,id))

def c37297 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37297 : Upper (D 6) (R 6) [34,129,257,48,68] 13 := by
  apply FastRouting.sound _ _ [34,129,257,48,68] 13 (by decide) (choices 1) [2,4,8,64] r37297 c37297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22401
  · exact u22402
  · exact u22403
  · exact u22404

def r37298 : Route 9 := (fun mask => (mask,id))

def c37298 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37298 : Upper (D 6) (R 6) [34,129,257,48,72] 13 := by
  apply FastRouting.sound _ _ [34,129,257,48,72] 13 (by decide) (choices 1) [2,4,64] r37298 c37298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22405
  · exact u22406
  · exact u22407

def r37299 : Route 9 := (fun mask => (mask,id))

def c37299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37299 : Upper (D 6) (R 6) [34,129,257,66,68] 13 := by
  apply FastRouting.sound _ _ [34,129,257,66,68] 13 (by decide) (choices 1) [4,8,16] r37299 c37299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22408
  · exact u22409
  · exact u22410

def b37300 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 261 74 88 52 116 180 308), lower := (rows 35 131 261 74 88 32 64 128 256), losses := [] }

theorem u37300 : Upper (D 6) (R 6) [34,129,257,66,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37301 : Route 9 := (fun mask => (mask,id))

def c37301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37301 : Upper (D 6) (R 6) [34,129,257,66,96] 13 := by
  apply FastRouting.sound _ _ [34,129,257,66,96] 13 (by decide) (choices 1) [4,8,16] r37301 c37301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22411
  · exact u22412
  · exact u22413

def b37302 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 261 76 84 58 122 186 314), lower := (rows 35 131 261 76 84 32 64 128 256), losses := [] }

theorem u37302 : Upper (D 6) (R 6) [34,129,257,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37303 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 261 76 88 54 118 182 310), lower := (rows 35 131 261 76 88 32 64 128 256), losses := [] }

theorem u37303 : Upper (D 6) (R 6) [34,129,257,68,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37304 : Route 9 := (fun mask => (mask,id))

def c37304 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37304 : Upper (D 6) (R 6) [34,129,257,68,96] 13 := by
  apply FastRouting.sound _ _ [34,129,257,68,96] 13 (by decide) (choices 1) [2,4,8,16] r37304 c37304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22414
  · exact u22415
  · exact u22416
  · exact u22417

def b37305 : PairBound 9 := { available := 38, camps := [{ cop := 6, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 261 88 88 38 102 166 294), lower := (rows 35 131 261 88 88 32 64 128 256), losses := [] }

theorem u37305 : Upper (D 6) (R 6) [34,129,257,80,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37306 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 261 88 112 46 78 142 270), lower := (rows 35 131 261 88 112 32 64 128 256), losses := [] }

theorem u37306 : Upper (D 6) (R 6) [34,129,257,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37307 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 3 },{ cop := 3, region := 16, targets := 32 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 262 13 28 112 112 240 368), lower := (rows 35 131 262 13 28 32 64 128 256), losses := [] }

theorem u37307 : Upper (D 6) (R 6) [34,129,258,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37308 : Route 9 := (fun mask => (mask,id))

def c37308 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37308 : Upper (D 6) (R 6) [34,129,258,5,36] 13 := by
  apply FastRouting.sound _ _ [34,129,258,5,36] 13 (by decide) (choices 1) [8,16,64] r37308 c37308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22418
  · exact u22419
  · exact u22420

def r37309 : Route 9 := (fun mask => (mask,id))

def c37309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37309 : Upper (D 6) (R 6) [34,129,258,5,40] 13 := by
  apply FastRouting.sound _ _ [34,129,258,5,40] 13 (by decide) (choices 1) [4,16,64] r37309 c37309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22421
  · exact u22422
  · exact u22423

def r37310 : Route 9 := (fun mask => (mask,id))

def c37310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37310 : Upper (D 6) (R 6) [34,129,258,5,68] 13 := by
  apply FastRouting.sound _ _ [34,129,258,5,68] 13 (by decide) (choices 1) [8,16,64] r37310 c37310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22424
  · exact u22425
  · exact u22426

def r37311 : Route 9 := (fun mask => (mask,id))

def c37311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37311 : Upper (D 6) (R 6) [34,129,258,5,72] 13 := by
  apply FastRouting.sound _ _ [34,129,258,5,72] 13 (by decide) (choices 1) [4,16,64] r37311 c37311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22427
  · exact u22428
  · exact u22429

def r37312 : Route 9 := (fun mask => (mask,id))

def c37312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37312 : Upper (D 6) (R 6) [34,129,258,5,96] 13 := by
  apply FastRouting.sound _ _ [34,129,258,5,96] 13 (by decide) (choices 1) [4,8,16,64] r37312 c37312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22430
  · exact u22431
  · exact u22432
  · exact u22433

def r37313 : Route 9 := (fun mask => (mask,id))

def c37313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37313 : Upper (D 6) (R 6) [34,129,258,17,12] 13 := by
  apply FastRouting.sound _ _ [34,129,258,17,12] 13 (by decide) (choices 1) [4,64] r37313 c37313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22434
  · exact u22435

def r37314 : Route 9 := (fun mask => (mask,id))

def c37314 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37314 : Upper (D 6) (R 6) [34,129,258,17,36] 13 := by
  apply FastRouting.sound _ _ [34,129,258,17,36] 13 (by decide) (choices 1) [4,8,64] r37314 c37314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22436
  · exact u22437
  · exact u22438

def b37315 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 262 25 56 100 68 196 324), lower := (rows 35 131 262 25 56 32 64 128 256), losses := [] }

theorem u37315 : Upper (D 6) (R 6) [34,129,258,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37316 : Route 9 := (fun mask => (mask,id))

def c37316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37316 : Upper (D 6) (R 6) [34,129,258,17,68] 13 := by
  apply FastRouting.sound _ _ [34,129,258,17,68] 13 (by decide) (choices 1) [4,8,64] r37316 c37316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22439
  · exact u22440
  · exact u22441

def r37317 : Route 9 := (fun mask => (mask,id))

def c37317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37317 : Upper (D 6) (R 6) [34,129,258,17,72] 13 := by
  apply FastRouting.sound _ _ [34,129,258,17,72] 13 (by decide) (choices 1) [4,64] r37317 c37317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22442
  · exact u22443

def r37318 : Route 9 := (fun mask => (mask,id))

def c37318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37318 : Upper (D 6) (R 6) [34,129,258,17,96] 13 := by
  apply FastRouting.sound _ _ [34,129,258,17,96] 13 (by decide) (choices 1) [4,8,64] r37318 c37318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22444
  · exact u22445
  · exact u22446

def b37319 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 262 28 28 97 97 225 353), lower := (rows 35 131 262 28 28 32 64 128 256), losses := [] }

theorem u37319 : Upper (D 6) (R 6) [34,129,258,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u37319
end Delivery.IrregularNine14.P06
