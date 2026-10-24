import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0391
import IrregularNine14P07C0392
import IrregularNine14P07C0393

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37260 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 13 26 274 225 193 193 449), lower := (rows 37 98 13 26 274 32 64 128 256), losses := [] }

theorem u37260 : Upper (D 7) (R 7) [36,96,9,18,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37261 : Route 9 := (fun mask => (mask,id))

def c37261 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37261 : Upper (D 7) (R 7) [36,96,9,18,320] 13 := by
  apply FastRouting.sound _ _ [36,96,9,18,320] 13 (by decide) (choices 1) [1,2,128] r37261 c37261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23489
  · exact u23490
  · exact u23491

def r37262 : Route 9 := (fun mask => (mask,id))

def c37262 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37262 : Upper (D 7) (R 7) [36,96,9,18,384] 13 := by
  apply FastRouting.sound _ _ [36,96,9,18,384] 13 (by decide) (choices 1) [1,2,64,128] r37262 c37262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23492
  · exact u23493
  · exact u23494
  · exact u23495

def b37263 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 13 88 19 418 450 386 386), lower := (rows 37 98 13 88 19 32 64 128 256), losses := [] }

theorem u37263 : Upper (D 7) (R 7) [36,96,9,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37264 : Route 9 := (fun mask => (mask,id))

def c37264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37264 : Upper (D 7) (R 7) [36,96,9,80,129] 13 := by
  apply FastRouting.sound _ _ [36,96,9,80,129] 13 (by decide) (choices 1) [2,128,256] r37264 c37264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23496
  · exact u23497
  · exact u23498

def r37265 : Route 9 := (fun mask => (mask,id))

def c37265 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37265 : Upper (D 7) (R 7) [36,96,9,80,130] 13 := by
  apply FastRouting.sound _ _ [36,96,9,80,130] 13 (by decide) (choices 1) [1,2,128,256] r37265 c37265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23499
  · exact u23500
  · exact u23501
  · exact u23502

def r37266 : Route 9 := (fun mask => (mask,id))

def c37266 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37266 : Upper (D 7) (R 7) [36,96,9,80,257] 13 := by
  apply FastRouting.sound _ _ [36,96,9,80,257] 13 (by decide) (choices 1) [2,128] r37266 c37266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23503
  · exact u23504

def r37267 : Route 9 := (fun mask => (mask,id))

def c37267 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37267 : Upper (D 7) (R 7) [36,96,9,80,258] 13 := by
  apply FastRouting.sound _ _ [36,96,9,80,258] 13 (by decide) (choices 1) [1,2,128] r37267 c37267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23505
  · exact u23506
  · exact u23507

def r37268 : Route 9 := (fun mask => (mask,id))

def c37268 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37268 : Upper (D 7) (R 7) [36,96,9,80,384] 13 := by
  apply FastRouting.sound _ _ [36,96,9,80,384] 13 (by decide) (choices 1) [1,2,128] r37268 c37268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23508
  · exact u23509
  · exact u23510

def b37269 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 13 138 19 496 464 464 464), lower := (rows 37 98 13 138 19 32 64 128 256), losses := [] }

theorem u37269 : Upper (D 7) (R 7) [36,96,9,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37270 : Route 9 := (fun mask => (mask,id))

def c37270 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u37270 : Upper (D 7) (R 7) [36,96,9,130,65] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,65] 13 (by decide) (choices 1) [2,16,128,256] r37270 c37270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23511
  · exact u23512
  · exact u23513
  · exact u23514

def b37271 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 13 138 82 433 465 401 401), lower := (rows 37 98 13 138 82 32 64 128 256), losses := [] }

theorem u37271 : Upper (D 7) (R 7) [36,96,9,130,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37272 : Route 9 := (fun mask => (mask,id))

def c37272 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37272 : Upper (D 7) (R 7) [36,96,9,130,129] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,129] 13 (by decide) (choices 1) [2,16,64,256] r37272 c37272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23515
  · exact u23516
  · exact u23517
  · exact u23518

def b37273 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 98 13 138 146 369 337 465 337), lower := (rows 37 98 13 138 146 32 64 128 256), losses := [] }

theorem u37273 : Upper (D 7) (R 7) [36,96,9,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37274 : Route 9 := (fun mask => (mask,id))

def c37274 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37274 : Upper (D 7) (R 7) [36,96,9,130,192] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,192] 13 (by decide) (choices 1) [1,2,16,256] r37274 c37274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23519
  · exact u23520
  · exact u23521
  · exact u23522

def r37275 : Route 9 := (fun mask => (mask,id))

def c37275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37275 : Upper (D 7) (R 7) [36,96,9,130,257] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,257] 13 (by decide) (choices 1) [2,16,64,128] r37275 c37275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23523
  · exact u23524
  · exact u23525
  · exact u23526

def r37276 : Route 9 := (fun mask => (mask,id))

def c37276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37276 : Upper (D 7) (R 7) [36,96,9,130,258] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,258] 13 (by decide) (choices 1) [1,16,64,128] r37276 c37276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23527
  · exact u23528
  · exact u23529
  · exact u23530

def r37277 : Route 9 := (fun mask => (mask,id))

def c37277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37277 : Upper (D 7) (R 7) [36,96,9,130,320] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,320] 13 (by decide) (choices 1) [1,2,16,128] r37277 c37277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23531
  · exact u23532
  · exact u23533
  · exact u23534

def r37278 : Route 9 := (fun mask => (mask,id))

def c37278 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37278 : Upper (D 7) (R 7) [36,96,9,130,384] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,384] 13 (by decide) (choices 1) [1,2,16,64] r37278 c37278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23535
  · exact u23536
  · exact u23537
  · exact u23538

def b37279 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 13 152 19 482 450 450 450), lower := (rows 37 98 13 152 19 32 64 128 256), losses := [] }

theorem u37279 : Upper (D 7) (R 7) [36,96,9,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37280 : Route 9 := (fun mask => (mask,id))

def c37280 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37280 : Upper (D 7) (R 7) [36,96,9,144,65] 13 := by
  apply FastRouting.sound _ _ [36,96,9,144,65] 13 (by decide) (choices 1) [2,128,256] r37280 c37280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23539
  · exact u23540
  · exact u23541

def b37281 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 13 152 82 419 451 387 387), lower := (rows 37 98 13 152 82 32 64 128 256), losses := [] }

theorem u37281 : Upper (D 7) (R 7) [36,96,9,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37282 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 37 98 13 152 145 354 322 450 322), lower := (rows 37 98 13 152 145 32 64 128 256), losses := [] }

theorem u37282 : Upper (D 7) (R 7) [36,96,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37283 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 13 152 146 355 323 451 323), lower := (rows 37 98 13 152 146 32 64 128 256), losses := [] }

theorem u37283 : Upper (D 7) (R 7) [36,96,9,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37284 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 13 152 208 291 323 387 259), lower := (rows 37 98 13 152 208 32 64 128 256), losses := [] }

theorem u37284 : Upper (D 7) (R 7) [36,96,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37285 : Route 9 := (fun mask => (mask,id))

def c37285 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37285 : Upper (D 7) (R 7) [36,96,9,144,257] 13 := by
  apply FastRouting.sound _ _ [36,96,9,144,257] 13 (by decide) (choices 1) [2,64,128] r37285 c37285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23542
  · exact u23543
  · exact u23544

def r37286 : Route 9 := (fun mask => (mask,id))

def c37286 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37286 : Upper (D 7) (R 7) [36,96,9,144,258] 13 := by
  apply FastRouting.sound _ _ [36,96,9,144,258] 13 (by decide) (choices 1) [1,2,64,128] r37286 c37286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23545
  · exact u23546
  · exact u23547
  · exact u23548

def r37287 : Route 9 := (fun mask => (mask,id))

def c37287 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37287 : Upper (D 7) (R 7) [36,96,9,144,320] 13 := by
  apply FastRouting.sound _ _ [36,96,9,144,320] 13 (by decide) (choices 1) [1,2,128] r37287 c37287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23549
  · exact u23550
  · exact u23551

def b37288 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 13 152 400 99 67 195 323), lower := (rows 37 98 13 152 400 32 64 128 256), losses := [] }

theorem u37288 : Upper (D 7) (R 7) [36,96,9,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37289 : PairBound 9 := { available := 402, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 13 200 19 434 466 402 402), lower := (rows 37 98 13 200 19 32 64 128 256), losses := [] }

theorem u37289 : Upper (D 7) (R 7) [36,96,9,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37290 : Route 9 := (fun mask => (mask,id))

def c37290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37290 : Upper (D 7) (R 7) [36,96,9,192,129] 13 := by
  apply FastRouting.sound _ _ [36,96,9,192,129] 13 (by decide) (choices 1) [2,16,256] r37290 c37290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23552
  · exact u23553
  · exact u23554

def r37291 : Route 9 := (fun mask => (mask,id))

def c37291 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37291 : Upper (D 7) (R 7) [36,96,9,192,130] 13 := by
  apply FastRouting.sound _ _ [36,96,9,192,130] 13 (by decide) (choices 1) [1,2,16,256] r37291 c37291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23555
  · exact u23556
  · exact u23557
  · exact u23558

def r37292 : Route 9 := (fun mask => (mask,id))

def c37292 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37292 : Upper (D 7) (R 7) [36,96,9,192,257] 13 := by
  apply FastRouting.sound _ _ [36,96,9,192,257] 13 (by decide) (choices 1) [2,16,128] r37292 c37292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23559
  · exact u23560
  · exact u23561

def r37293 : Route 9 := (fun mask => (mask,id))

def c37293 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37293 : Upper (D 7) (R 7) [36,96,9,192,258] 13 := by
  apply FastRouting.sound _ _ [36,96,9,192,258] 13 (by decide) (choices 1) [1,2,16,128] r37293 c37293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23562
  · exact u23563
  · exact u23564
  · exact u23565

def r37294 : Route 9 := (fun mask => (mask,id))

def c37294 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37294 : Upper (D 7) (R 7) [36,96,9,192,384] 13 := by
  apply FastRouting.sound _ _ [36,96,9,192,384] 13 (by decide) (choices 1) [1,2,16] r37294 c37294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23566
  · exact u23567
  · exact u23568

def b37295 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 13 266 19 240 208 208 464), lower := (rows 37 98 13 266 19 32 64 128 256), losses := [] }

theorem u37295 : Upper (D 7) (R 7) [36,96,9,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37296 : Route 9 := (fun mask => (mask,id))

def c37296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37296 : Upper (D 7) (R 7) [36,96,9,258,65] 13 := by
  apply FastRouting.sound _ _ [36,96,9,258,65] 13 (by decide) (choices 1) [2,16,128] r37296 c37296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23569
  · exact u23570
  · exact u23571

def b37297 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 13 266 82 177 209 145 401), lower := (rows 37 98 13 266 82 32 64 128 256), losses := [] }

theorem u37297 : Upper (D 7) (R 7) [36,96,9,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37298 : Route 9 := (fun mask => (mask,id))

def c37298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37298 : Upper (D 7) (R 7) [36,96,9,258,129] 13 := by
  apply FastRouting.sound _ _ [36,96,9,258,129] 13 (by decide) (choices 1) [2,16,64,128] r37298 c37298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23572
  · exact u23573
  · exact u23574
  · exact u23575

def r37299 : Route 9 := (fun mask => (mask,id))

def c37299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37299 : Upper (D 7) (R 7) [36,96,9,258,130] 13 := by
  apply FastRouting.sound _ _ [36,96,9,258,130] 13 (by decide) (choices 1) [1,16,64,128] r37299 c37299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23576
  · exact u23577
  · exact u23578
  · exact u23579

def r37300 : Route 9 := (fun mask => (mask,id))

def c37300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37300 : Upper (D 7) (R 7) [36,96,9,258,192] 13 := by
  apply FastRouting.sound _ _ [36,96,9,258,192] 13 (by decide) (choices 1) [1,2,16,128] r37300 c37300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23580
  · exact u23581
  · exact u23582
  · exact u23583

def b37301 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 13 280 19 226 194 194 450), lower := (rows 37 98 13 280 19 32 64 128 256), losses := [] }

theorem u37301 : Upper (D 7) (R 7) [36,96,9,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37302 : Route 9 := (fun mask => (mask,id))

def c37302 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37302 : Upper (D 7) (R 7) [36,96,9,272,65] 13 := by
  apply FastRouting.sound _ _ [36,96,9,272,65] 13 (by decide) (choices 1) [2,128] r37302 c37302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23584
  · exact u23585

def b37303 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 13 280 82 163 195 131 387), lower := (rows 37 98 13 280 82 32 64 128 256), losses := [] }

theorem u37303 : Upper (D 7) (R 7) [36,96,9,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37304 : Route 9 := (fun mask => (mask,id))

def c37304 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37304 : Upper (D 7) (R 7) [36,96,9,272,129] 13 := by
  apply FastRouting.sound _ _ [36,96,9,272,129] 13 (by decide) (choices 1) [2,64,128] r37304 c37304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23586
  · exact u23587
  · exact u23588

def r37305 : Route 9 := (fun mask => (mask,id))

def c37305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37305 : Upper (D 7) (R 7) [36,96,9,272,130] 13 := by
  apply FastRouting.sound _ _ [36,96,9,272,130] 13 (by decide) (choices 1) [1,2,64,128] r37305 c37305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23589
  · exact u23590
  · exact u23591
  · exact u23592

def r37306 : Route 9 := (fun mask => (mask,id))

def c37306 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37306 : Upper (D 7) (R 7) [36,96,9,272,192] 13 := by
  apply FastRouting.sound _ _ [36,96,9,272,192] 13 (by decide) (choices 1) [1,2,128] r37306 c37306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23593
  · exact u23594
  · exact u23595

def b37307 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 13 328 19 178 210 146 402), lower := (rows 37 98 13 328 19 32 64 128 256), losses := [] }

theorem u37307 : Upper (D 7) (R 7) [36,96,9,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37308 : Route 9 := (fun mask => (mask,id))

def c37308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37308 : Upper (D 7) (R 7) [36,96,9,320,129] 13 := by
  apply FastRouting.sound _ _ [36,96,9,320,129] 13 (by decide) (choices 1) [2,16,128] r37308 c37308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23596
  · exact u23597
  · exact u23598

def r37309 : Route 9 := (fun mask => (mask,id))

def c37309 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37309 : Upper (D 7) (R 7) [36,96,9,320,130] 13 := by
  apply FastRouting.sound _ _ [36,96,9,320,130] 13 (by decide) (choices 1) [1,2,16,128] r37309 c37309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23599
  · exact u23600
  · exact u23601
  · exact u23602

def b37310 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 13 392 19 242 210 210 466), lower := (rows 37 98 13 392 19 32 64 128 256), losses := [] }

theorem u37310 : Upper (D 7) (R 7) [36,96,9,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37311 : Route 9 := (fun mask => (mask,id))

def c37311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37311 : Upper (D 7) (R 7) [36,96,9,384,65] 13 := by
  apply FastRouting.sound _ _ [36,96,9,384,65] 13 (by decide) (choices 1) [2,16,128] r37311 c37311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23603
  · exact u23604
  · exact u23605

def b37312 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 13 392 82 179 211 147 403), lower := (rows 37 98 13 392 82 32 64 128 256), losses := [] }

theorem u37312 : Upper (D 7) (R 7) [36,96,9,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37313 : Route 9 := (fun mask => (mask,id))

def c37313 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37313 : Upper (D 7) (R 7) [36,96,9,384,129] 13 := by
  apply FastRouting.sound _ _ [36,96,9,384,129] 13 (by decide) (choices 1) [2,16,64] r37313 c37313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23606
  · exact u23607
  · exact u23608

def r37314 : Route 9 := (fun mask => (mask,id))

def c37314 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37314 : Upper (D 7) (R 7) [36,96,9,384,130] 13 := by
  apply FastRouting.sound _ _ [36,96,9,384,130] 13 (by decide) (choices 1) [1,2,16,64] r37314 c37314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23609
  · exact u23610
  · exact u23611
  · exact u23612

def r37315 : Route 9 := (fun mask => (mask,id))

def c37315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37315 : Upper (D 7) (R 7) [36,96,9,384,192] 13 := by
  apply FastRouting.sound _ _ [36,96,9,384,192] 13 (by decide) (choices 1) [1,2,16] r37315 c37315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23613
  · exact u23614
  · exact u23615

def b37316 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 14 25 19 480 448 448 448), lower := (rows 37 98 14 25 19 32 64 128 256), losses := [] }

theorem u37316 : Upper (D 7) (R 7) [36,96,10,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37317 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 14 25 81 418 450 386 386), lower := (rows 37 98 14 25 81 32 64 128 256), losses := [] }

theorem u37317 : Upper (D 7) (R 7) [36,96,10,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37318 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 14 25 82 417 449 385 385), lower := (rows 37 98 14 25 82 32 64 128 256), losses := [] }

theorem u37318 : Upper (D 7) (R 7) [36,96,10,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37319 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 14 25 145 482 450 450 450), lower := (rows 37 98 14 25 145 32 64 128 256), losses := [] }

theorem u37319 : Upper (D 7) (R 7) [36,96,10,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u37319
end Delivery.IrregularNine14.P07
