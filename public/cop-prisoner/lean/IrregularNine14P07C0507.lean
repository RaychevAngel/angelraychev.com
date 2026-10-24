import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0204
import IrregularNine14P07C0205
import IrregularNine14P07C0206

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30420 : Route 9 := (fun mask => (mask,id))

def c30420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30420 : Upper (D 7) (R 7) [6,33,72,129,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,384] 13 (by decide) (choices 1) [2,16,64] r30420 c30420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12270
  · exact u12271
  · exact u12272

def b30421 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 35 76 138 49 496 464 464 464), lower := (rows 7 35 76 138 49 32 64 128 256), losses := [] }

theorem u30421 : Upper (D 7) (R 7) [6,33,72,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30422 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 496, targets := 2 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 35 76 138 81 432 496 432 432), lower := (rows 7 35 76 138 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 19 59 91 155 283), good := (rows 501 497 492 508 497 32 64 128 256) }] }

theorem u30422 : Upper (D 7) (R 7) [6,33,72,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30423 : Route 9 := (fun mask => (mask,id))

def c30423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30423 : Upper (D 7) (R 7) [6,33,72,130,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,96] 13 (by decide) (choices 1) [1,16,128,256] r30423 c30423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12273
  · exact u12274
  · exact u12275
  · exact u12276

def r30424 : Route 9 := (fun mask => (mask,id))

def c30424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30424 : Upper (D 7) (R 7) [6,33,72,130,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,129] 13 (by decide) (choices 1) [16,64,256] r30424 c30424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12277
  · exact u12278
  · exact u12279

def r30425 : Route 9 := (fun mask => (mask,id))

def c30425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30425 : Upper (D 7) (R 7) [6,33,72,130,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,160] 13 (by decide) (choices 1) [1,16,64,256] r30425 c30425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12280
  · exact u12281
  · exact u12282
  · exact u12283

def r30426 : Route 9 := (fun mask => (mask,id))

def c30426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30426 : Upper (D 7) (R 7) [6,33,72,130,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,192] 13 (by decide) (choices 1) [1,16,256] r30426 c30426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12284
  · exact u12285
  · exact u12286

def r30427 : Route 9 := (fun mask => (mask,id))

def c30427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30427 : Upper (D 7) (R 7) [6,33,72,130,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,257] 13 (by decide) (choices 1) [16,64,128] r30427 c30427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12287
  · exact u12288
  · exact u12289

def r30428 : Route 9 := (fun mask => (mask,id))

def c30428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30428 : Upper (D 7) (R 7) [6,33,72,130,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,288] 13 (by decide) (choices 1) [1,16,64,128] r30428 c30428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12290
  · exact u12291
  · exact u12292
  · exact u12293

def r30429 : Route 9 := (fun mask => (mask,id))

def c30429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30429 : Upper (D 7) (R 7) [6,33,72,130,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,320] 13 (by decide) (choices 1) [1,16,128] r30429 c30429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12294
  · exact u12295
  · exact u12296

def r30430 : Route 9 := (fun mask => (mask,id))

def c30430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30430 : Upper (D 7) (R 7) [6,33,72,130,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,384] 13 (by decide) (choices 1) [1,16,64] r30430 c30430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12297
  · exact u12298
  · exact u12299

def b30431 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 76 152 19 480 480 480 480), lower := (rows 7 35 76 152 19 32 64 128 256), losses := [] }

theorem u30431 : Upper (D 7) (R 7) [6,33,72,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30432 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 35 76 152 49 482 450 450 450), lower := (rows 7 35 76 152 49 32 64 128 256), losses := [] }

theorem u30432 : Upper (D 7) (R 7) [6,33,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30433 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 35 76 152 50 481 449 449 449), lower := (rows 7 35 76 152 50 32 64 128 256), losses := [] }

theorem u30433 : Upper (D 7) (R 7) [6,33,72,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30434 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 35 76 152 81 418 482 418 418), lower := (rows 7 35 76 152 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 486 482 76 156 508 32 64 128 256) }] }

theorem u30434 : Upper (D 7) (R 7) [6,33,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30435 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(2,1),(3,1)], upper := (rows 7 35 76 152 82 417 481 417 417), lower := (rows 7 35 76 152 82 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 485 481 76 156 508 32 64 128 256) }] }

theorem u30435 : Upper (D 7) (R 7) [6,33,72,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30436 : Route 9 := (fun mask => (mask,id))

def c30436 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30436 : Upper (D 7) (R 7) [6,33,72,144,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,96] 13 (by decide) (choices 1) [1,2,128,256] r30436 c30436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12300
  · exact u12301
  · exact u12302
  · exact u12303

def b30437 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 35 76 152 145 354 354 482 354), lower := (rows 7 35 76 152 145 32 64 128 256), losses := [] }

theorem u30437 : Upper (D 7) (R 7) [6,33,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30438 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 35 76 152 146 353 353 481 353), lower := (rows 7 35 76 152 146 32 64 128 256), losses := [] }

theorem u30438 : Upper (D 7) (R 7) [6,33,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30439 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 35 76 152 176 355 323 451 323), lower := (rows 7 35 76 152 176 32 64 128 256), losses := [] }

theorem u30439 : Upper (D 7) (R 7) [6,33,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30440 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(3,0)], upper := (rows 7 35 76 152 208 291 355 419 291), lower := (rows 7 35 76 152 208 32 64 128 256), losses := [] }

theorem u30440 : Upper (D 7) (R 7) [6,33,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30441 : Route 9 := (fun mask => (mask,id))

def c30441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30441 : Upper (D 7) (R 7) [6,33,72,144,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,257] 13 (by decide) (choices 1) [2,64,128] r30441 c30441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12304
  · exact u12305
  · exact u12306

def r30442 : Route 9 := (fun mask => (mask,id))

def c30442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30442 : Upper (D 7) (R 7) [6,33,72,144,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,258] 13 (by decide) (choices 1) [1,64,128] r30442 c30442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12307
  · exact u12308
  · exact u12309

def r30443 : Route 9 := (fun mask => (mask,id))

def c30443 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30443 : Upper (D 7) (R 7) [6,33,72,144,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,288] 13 (by decide) (choices 1) [1,2,64,128] r30443 c30443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12310
  · exact u12311
  · exact u12312
  · exact u12313

def r30444 : Route 9 := (fun mask => (mask,id))

def c30444 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30444 : Upper (D 7) (R 7) [6,33,72,144,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,320] 13 (by decide) (choices 1) [1,2,128] r30444 c30444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12314
  · exact u12315
  · exact u12316

def b30445 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 35 76 152 400 99 99 227 355), lower := (rows 7 35 76 152 400 32 64 128 256), losses := [] }

theorem u30445 : Upper (D 7) (R 7) [6,33,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30446 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 76 168 19 496 464 464 464), lower := (rows 7 35 76 168 19 32 64 128 256), losses := [] }

theorem u30446 : Upper (D 7) (R 7) [6,33,72,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30447 : Route 9 := (fun mask => (mask,id))

def c30447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30447 : Upper (D 7) (R 7) [6,33,72,160,65] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,65] 13 (by decide) (choices 1) [2,16,128,256] r30447 c30447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12317
  · exact u12318
  · exact u12319
  · exact u12320

def r30448 : Route 9 := (fun mask => (mask,id))

def c30448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30448 : Upper (D 7) (R 7) [6,33,72,160,66] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,66] 13 (by decide) (choices 1) [1,16,128,256] r30448 c30448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12321
  · exact u12322
  · exact u12323
  · exact u12324

def r30449 : Route 9 := (fun mask => (mask,id))

def c30449 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30449 : Upper (D 7) (R 7) [6,33,72,160,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,129] 13 (by decide) (choices 1) [2,16,64,256] r30449 c30449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12325
  · exact u12326
  · exact u12327
  · exact u12328

def r30450 : Route 9 := (fun mask => (mask,id))

def c30450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30450 : Upper (D 7) (R 7) [6,33,72,160,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,130] 13 (by decide) (choices 1) [1,16,64,256] r30450 c30450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12329
  · exact u12330
  · exact u12331
  · exact u12332

def r30451 : Route 9 := (fun mask => (mask,id))

def c30451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30451 : Upper (D 7) (R 7) [6,33,72,160,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,192] 13 (by decide) (choices 1) [1,2,16,256] r30451 c30451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12333
  · exact u12334
  · exact u12335
  · exact u12336

def r30452 : Route 9 := (fun mask => (mask,id))

def c30452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30452 : Upper (D 7) (R 7) [6,33,72,160,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,257] 13 (by decide) (choices 1) [2,16,64,128] r30452 c30452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12337
  · exact u12338
  · exact u12339
  · exact u12340

def r30453 : Route 9 := (fun mask => (mask,id))

def c30453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30453 : Upper (D 7) (R 7) [6,33,72,160,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,258] 13 (by decide) (choices 1) [1,16,64,128] r30453 c30453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12341
  · exact u12342
  · exact u12343
  · exact u12344

def r30454 : Route 9 := (fun mask => (mask,id))

def c30454 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30454 : Upper (D 7) (R 7) [6,33,72,160,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,320] 13 (by decide) (choices 1) [1,2,16,128] r30454 c30454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12345
  · exact u12346
  · exact u12347
  · exact u12348

def r30455 : Route 9 := (fun mask => (mask,id))

def c30455 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30455 : Upper (D 7) (R 7) [6,33,72,160,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,384] 13 (by decide) (choices 1) [1,2,16,64] r30455 c30455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12349
  · exact u12350
  · exact u12351
  · exact u12352

def b30456 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 16, targets := 64 }], pairs := [(0,5),(2,5),(3,5),(4,6)], upper := (rows 7 35 76 265 50 240 208 208 464), lower := (rows 7 35 76 265 50 32 64 128 256), losses := [] }

theorem u30456 : Upper (D 7) (R 7) [6,33,72,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30457 : Route 9 := (fun mask => (mask,id))

def c30457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30457 : Upper (D 7) (R 7) [6,33,72,257,66] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,66] 13 (by decide) (choices 1) [16,128] r30457 c30457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12353
  · exact u12354

def r30458 : Route 9 := (fun mask => (mask,id))

def c30458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30458 : Upper (D 7) (R 7) [6,33,72,257,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,96] 13 (by decide) (choices 1) [2,16,128] r30458 c30458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12355
  · exact u12356
  · exact u12357

def r30459 : Route 9 := (fun mask => (mask,id))

def c30459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30459 : Upper (D 7) (R 7) [6,33,72,257,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,130] 13 (by decide) (choices 1) [16,64,128] r30459 c30459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12358
  · exact u12359
  · exact u12360

def r30460 : Route 9 := (fun mask => (mask,id))

def c30460 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30460 : Upper (D 7) (R 7) [6,33,72,257,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,160] 13 (by decide) (choices 1) [2,16,64,128] r30460 c30460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12361
  · exact u12362
  · exact u12363
  · exact u12364

def r30461 : Route 9 := (fun mask => (mask,id))

def c30461 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30461 : Upper (D 7) (R 7) [6,33,72,257,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,192] 13 (by decide) (choices 1) [2,16,128] r30461 c30461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12365
  · exact u12366
  · exact u12367

def b30462 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 35 76 266 49 240 208 208 464), lower := (rows 7 35 76 266 49 32 64 128 256), losses := [] }

theorem u30462 : Upper (D 7) (R 7) [6,33,72,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30463 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 35 76 266 81 176 240 176 432), lower := (rows 7 35 76 266 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 19 59 91 155 283), good := (rows 501 497 492 508 497 32 64 128 256) }] }

theorem u30463 : Upper (D 7) (R 7) [6,33,72,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30464 : Route 9 := (fun mask => (mask,id))

def c30464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30464 : Upper (D 7) (R 7) [6,33,72,258,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,258,96] 13 (by decide) (choices 1) [1,16,128] r30464 c30464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12368
  · exact u12369
  · exact u12370

def r30465 : Route 9 := (fun mask => (mask,id))

def c30465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30465 : Upper (D 7) (R 7) [6,33,72,258,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,258,129] 13 (by decide) (choices 1) [16,64,128] r30465 c30465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12371
  · exact u12372
  · exact u12373

def r30466 : Route 9 := (fun mask => (mask,id))

def c30466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30466 : Upper (D 7) (R 7) [6,33,72,258,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,258,160] 13 (by decide) (choices 1) [1,16,64,128] r30466 c30466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12374
  · exact u12375
  · exact u12376
  · exact u12377

def r30467 : Route 9 := (fun mask => (mask,id))

def c30467 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30467 : Upper (D 7) (R 7) [6,33,72,258,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,258,192] 13 (by decide) (choices 1) [1,16,128] r30467 c30467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12378
  · exact u12379
  · exact u12380

def b30468 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 76 280 19 224 224 224 480), lower := (rows 7 35 76 280 19 32 64 128 256), losses := [] }

theorem u30468 : Upper (D 7) (R 7) [6,33,72,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30469 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 35 76 280 49 226 194 194 450), lower := (rows 7 35 76 280 49 32 64 128 256), losses := [] }

theorem u30469 : Upper (D 7) (R 7) [6,33,72,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30470 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 35 76 280 50 225 193 193 449), lower := (rows 7 35 76 280 50 32 64 128 256), losses := [] }

theorem u30470 : Upper (D 7) (R 7) [6,33,72,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30471 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 35 76 280 81 162 226 162 418), lower := (rows 7 35 76 280 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 486 482 76 284 508 32 64 128 256) }] }

theorem u30471 : Upper (D 7) (R 7) [6,33,72,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30472 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(2,1),(3,1)], upper := (rows 7 35 76 280 82 161 225 161 417), lower := (rows 7 35 76 280 82 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 485 481 76 284 508 32 64 128 256) }] }

theorem u30472 : Upper (D 7) (R 7) [6,33,72,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30473 : Route 9 := (fun mask => (mask,id))

def c30473 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30473 : Upper (D 7) (R 7) [6,33,72,272,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272,96] 13 (by decide) (choices 1) [1,2,128] r30473 c30473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12381
  · exact u12382
  · exact u12383

def r30474 : Route 9 := (fun mask => (mask,id))

def c30474 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30474 : Upper (D 7) (R 7) [6,33,72,272,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272,129] 13 (by decide) (choices 1) [2,64,128] r30474 c30474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12384
  · exact u12385
  · exact u12386

def r30475 : Route 9 := (fun mask => (mask,id))

def c30475 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30475 : Upper (D 7) (R 7) [6,33,72,272,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272,130] 13 (by decide) (choices 1) [1,64,128] r30475 c30475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12387
  · exact u12388
  · exact u12389

def r30476 : Route 9 := (fun mask => (mask,id))

def c30476 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30476 : Upper (D 7) (R 7) [6,33,72,272,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272,160] 13 (by decide) (choices 1) [1,2,64,128] r30476 c30476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12390
  · exact u12391
  · exact u12392
  · exact u12393

def r30477 : Route 9 := (fun mask => (mask,id))

def c30477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30477 : Upper (D 7) (R 7) [6,33,72,272,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272,192] 13 (by decide) (choices 1) [1,2,128] r30477 c30477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12394
  · exact u12395
  · exact u12396

def b30478 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 76 296 19 240 208 208 464), lower := (rows 7 35 76 296 19 32 64 128 256), losses := [] }

theorem u30478 : Upper (D 7) (R 7) [6,33,72,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30479 : Route 9 := (fun mask => (mask,id))

def c30479 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30479 : Upper (D 7) (R 7) [6,33,72,288,65] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,65] 13 (by decide) (choices 1) [2,16,128] r30479 c30479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12397
  · exact u12398
  · exact u12399

#print axioms u30479
end Delivery.IrregularNine14.P07
