import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0222
import IrregularNine14P06C0223
import IrregularNine14P06C0224

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31320 : Route 9 := (fun mask => (mask,id))

def c31320 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31320 : Upper (D 6) (R 6) [10,36,129,20,65] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,65] 13 (by decide) (choices 1) [2,64,256] r31320 c31320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13361
  · exact u13362
  · exact u13363

def r31321 : Route 9 := (fun mask => (mask,id))

def c31321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31321 : Upper (D 6) (R 6) [10,36,129,20,66] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,66] 13 (by decide) (choices 1) [1,64,256] r31321 c31321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13364
  · exact u13365
  · exact u13366

def r31322 : Route 9 := (fun mask => (mask,id))

def c31322 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31322 : Upper (D 6) (R 6) [10,36,129,20,96] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,96] 13 (by decide) (choices 1) [1,2,64,256] r31322 c31322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13367
  · exact u13368
  · exact u13369
  · exact u13370

def r31323 : Route 9 := (fun mask => (mask,id))

def c31323 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31323 : Upper (D 6) (R 6) [10,36,129,20,257] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,257] 13 (by decide) (choices 1) [2,64] r31323 c31323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13371
  · exact u13372

def r31324 : Route 9 := (fun mask => (mask,id))

def c31324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31324 : Upper (D 6) (R 6) [10,36,129,20,258] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,258] 13 (by decide) (choices 1) [1,64] r31324 c31324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13373
  · exact u13374

def r31325 : Route 9 := (fun mask => (mask,id))

def c31325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31325 : Upper (D 6) (R 6) [10,36,129,20,288] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,288] 13 (by decide) (choices 1) [1,2,64] r31325 c31325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13375
  · exact u13376
  · exact u13377

def r31326 : Route 9 := (fun mask => (mask,id))

def c31326 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31326 : Upper (D 6) (R 6) [10,36,129,20,320] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,320] 13 (by decide) (choices 1) [1,2,64] r31326 c31326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13378
  · exact u13379
  · exact u13380

def b31327 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 133 56 19 356 324 452 324), lower := (rows 11 38 133 56 19 32 64 128 256), losses := [] }

theorem u31327 : Upper (D 6) (R 6) [10,36,129,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31328 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 133 56 21 354 322 450 322), lower := (rows 11 38 133 56 21 32 64 128 256), losses := [] }

theorem u31328 : Upper (D 6) (R 6) [10,36,129,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31329 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 133 56 22 353 321 449 321), lower := (rows 11 38 133 56 22 32 64 128 256), losses := [] }

theorem u31329 : Upper (D 6) (R 6) [10,36,129,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31330 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 354, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 38 133 56 81 358 326 454 326), lower := (rows 11 38 133 56 81 32 64 128 256), losses := [] }

theorem u31330 : Upper (D 6) (R 6) [10,36,129,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31331 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 38 133 56 82 357 325 453 325), lower := (rows 11 38 133 56 82 32 64 128 256), losses := [] }

theorem u31331 : Upper (D 6) (R 6) [10,36,129,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31332 : Route 9 := (fun mask => (mask,id))

def c31332 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31332 : Upper (D 6) (R 6) [10,36,129,48,68] 13 := by
  apply FastRouting.sound _ _ [10,36,129,48,68] 13 (by decide) (choices 1) [1,2,64,256] r31332 c31332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13381
  · exact u13382
  · exact u13383
  · exact u13384

def b31333 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 38 133 56 273 102 70 198 326), lower := (rows 11 38 133 56 273 32 64 128 256), losses := [] }

theorem u31333 : Upper (D 6) (R 6) [10,36,129,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31334 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 38 133 56 274 101 69 197 325), lower := (rows 11 38 133 56 274 32 64 128 256), losses := [] }

theorem u31334 : Upper (D 6) (R 6) [10,36,129,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31335 : Route 9 := (fun mask => (mask,id))

def c31335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31335 : Upper (D 6) (R 6) [10,36,129,48,260] 13 := by
  apply FastRouting.sound _ _ [10,36,129,48,260] 13 (by decide) (choices 1) [1,2,64] r31335 c31335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13385
  · exact u13386
  · exact u13387

def r31336 : Route 9 := (fun mask => (mask,id))

def c31336 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31336 : Upper (D 6) (R 6) [10,36,129,48,320] 13 := by
  apply FastRouting.sound _ _ [10,36,129,48,320] 13 (by decide) (choices 1) [1,2,4,64] r31336 c31336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13388
  · exact u13389
  · exact u13390
  · exact u13391

def b31337 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 16, targets := 96 },{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 11 38 133 73 22 368 368 496 368), lower := (rows 11 38 133 73 22 32 64 128 256), losses := [] }

theorem u31337 : Upper (D 6) (R 6) [10,36,129,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31338 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 38 133 73 50 372 340 468 340), lower := (rows 11 38 133 73 50 32 64 128 256), losses := [] }

theorem u31338 : Upper (D 6) (R 6) [10,36,129,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31339 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 73 52 370 338 466 338), lower := (rows 11 38 133 73 52 32 64 128 256), losses := [] }

theorem u31339 : Upper (D 6) (R 6) [10,36,129,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31340 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 38 133 73 82 308 372 436 308), lower := (rows 11 38 133 73 82 32 64 128 256), losses := [] }

theorem u31340 : Upper (D 6) (R 6) [10,36,129,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31341 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 38 133 73 84 306 370 434 306), lower := (rows 11 38 133 73 84 32 64 128 256), losses := [] }

theorem u31341 : Upper (D 6) (R 6) [10,36,129,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31342 : Route 9 := (fun mask => (mask,id))

def c31342 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31342 : Upper (D 6) (R 6) [10,36,129,65,96] 13 := by
  apply FastRouting.sound _ _ [10,36,129,65,96] 13 (by decide) (choices 1) [2,4,16,256] r31342 c31342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13392
  · exact u13393
  · exact u13394
  · exact u13395

def r31343 : Route 9 := (fun mask => (mask,id))

def c31343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31343 : Upper (D 6) (R 6) [10,36,129,65,258] 13 := by
  apply FastRouting.sound _ _ [10,36,129,65,258] 13 (by decide) (choices 1) [4,16,64] r31343 c31343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13396
  · exact u13397
  · exact u13398

def r31344 : Route 9 := (fun mask => (mask,id))

def c31344 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31344 : Upper (D 6) (R 6) [10,36,129,65,260] 13 := by
  apply FastRouting.sound _ _ [10,36,129,65,260] 13 (by decide) (choices 1) [2,16,64] r31344 c31344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13399
  · exact u13400
  · exact u13401

def r31345 : Route 9 := (fun mask => (mask,id))

def c31345 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31345 : Upper (D 6) (R 6) [10,36,129,65,288] 13 := by
  apply FastRouting.sound _ _ [10,36,129,65,288] 13 (by decide) (choices 1) [2,4,16,64] r31345 c31345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13402
  · exact u13403
  · exact u13404
  · exact u13405

def r31346 : Route 9 := (fun mask => (mask,id))

def c31346 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31346 : Upper (D 6) (R 6) [10,36,129,65,320] 13 := by
  apply FastRouting.sound _ _ [10,36,129,65,320] 13 (by decide) (choices 1) [2,4,16] r31346 c31346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13406
  · exact u13407
  · exact u13408

def b31347 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 38 133 76 19 368 368 496 368), lower := (rows 11 38 133 76 19 32 64 128 256), losses := [] }

theorem u31347 : Upper (D 6) (R 6) [10,36,129,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31348 : Route 9 := (fun mask => (mask,id))

def c31348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u31348 : Upper (D 6) (R 6) [10,36,129,68,33] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,33] 13 (by decide) (choices 1) [2,16,64,256] r31348 c31348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13409
  · exact u13410
  · exact u13411
  · exact u13412

def b31349 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 133 76 50 369 337 465 337), lower := (rows 11 38 133 76 50 32 64 128 256), losses := [] }

theorem u31349 : Upper (D 6) (R 6) [10,36,129,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31350 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,6),(2,6),(4,2)], upper := (rows 11 38 133 76 81 306 370 434 306), lower := (rows 11 38 133 76 81 32 64 128 256), losses := [] }

theorem u31350 : Upper (D 6) (R 6) [10,36,129,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31351 : Route 9 := (fun mask => (mask,id))

def c31351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31351 : Upper (D 6) (R 6) [10,36,129,68,66] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,66] 13 (by decide) (choices 1) [1,16,256] r31351 c31351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13413
  · exact u13414
  · exact u13415

def r31352 : Route 9 := (fun mask => (mask,id))

def c31352 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31352 : Upper (D 6) (R 6) [10,36,129,68,96] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,96] 13 (by decide) (choices 1) [1,2,16,256] r31352 c31352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13416
  · exact u13417
  · exact u13418
  · exact u13419

def r31353 : Route 9 := (fun mask => (mask,id))

def c31353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31353 : Upper (D 6) (R 6) [10,36,129,68,257] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,257] 13 (by decide) (choices 1) [2,16,64] r31353 c31353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13420
  · exact u13421
  · exact u13422

def r31354 : Route 9 := (fun mask => (mask,id))

def c31354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31354 : Upper (D 6) (R 6) [10,36,129,68,258] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,258] 13 (by decide) (choices 1) [1,16,64] r31354 c31354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13423
  · exact u13424
  · exact u13425

def r31355 : Route 9 := (fun mask => (mask,id))

def c31355 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31355 : Upper (D 6) (R 6) [10,36,129,68,288] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,288] 13 (by decide) (choices 1) [1,2,16,64] r31355 c31355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13426
  · exact u13427
  · exact u13428
  · exact u13429

def r31356 : Route 9 := (fun mask => (mask,id))

def c31356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31356 : Upper (D 6) (R 6) [10,36,129,68,320] 13 := by
  apply FastRouting.sound _ _ [10,36,129,68,320] 13 (by decide) (choices 1) [1,2,16] r31356 c31356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13430
  · exact u13431
  · exact u13432

def b31357 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 133 88 19 356 356 484 356), lower := (rows 11 38 133 88 19 32 64 128 256), losses := [] }

theorem u31357 : Upper (D 6) (R 6) [10,36,129,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31358 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 38 133 88 21 354 354 482 354), lower := (rows 11 38 133 88 21 32 64 128 256), losses := [] }

theorem u31358 : Upper (D 6) (R 6) [10,36,129,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31359 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 133 88 22 353 353 481 353), lower := (rows 11 38 133 88 22 32 64 128 256), losses := [] }

theorem u31359 : Upper (D 6) (R 6) [10,36,129,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31360 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 452, targets := 32 },{ cop := 2, region := 354, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 11 38 133 88 49 358 326 454 326), lower := (rows 11 38 133 88 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 24 16 0 67 131 259), good := (rows 463 454 453 92 477 0 64 128 256) }] }

theorem u31360 : Upper (D 6) (R 6) [10,36,129,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31361 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 133 88 50 357 325 453 325), lower := (rows 11 38 133 88 50 32 64 128 256), losses := [] }

theorem u31361 : Upper (D 6) (R 6) [10,36,129,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31362 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 133 88 52 355 323 451 323), lower := (rows 11 38 133 88 52 32 64 128 256), losses := [] }

theorem u31362 : Upper (D 6) (R 6) [10,36,129,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31363 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 38 133 88 81 294 358 422 294), lower := (rows 11 38 133 88 81 32 64 128 256), losses := [] }

theorem u31363 : Upper (D 6) (R 6) [10,36,129,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31364 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 38 133 88 82 293 357 421 293), lower := (rows 11 38 133 88 82 32 64 128 256), losses := [] }

theorem u31364 : Upper (D 6) (R 6) [10,36,129,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31365 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 38 133 88 84 291 355 419 291), lower := (rows 11 38 133 88 84 32 64 128 256), losses := [] }

theorem u31365 : Upper (D 6) (R 6) [10,36,129,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31366 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 38 133 88 112 295 327 391 263), lower := (rows 11 38 133 88 112 32 64 128 256), losses := [] }

theorem u31366 : Upper (D 6) (R 6) [10,36,129,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31367 : Route 9 := (fun mask => (mask,id))

def c31367 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31367 : Upper (D 6) (R 6) [10,36,129,80,257] 13 := by
  apply FastRouting.sound _ _ [10,36,129,80,257] 13 (by decide) (choices 1) [2,4,64] r31367 c31367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13433
  · exact u13434
  · exact u13435

def r31368 : Route 9 := (fun mask => (mask,id))

def c31368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31368 : Upper (D 6) (R 6) [10,36,129,80,258] 13 := by
  apply FastRouting.sound _ _ [10,36,129,80,258] 13 (by decide) (choices 1) [1,4,64] r31368 c31368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13436
  · exact u13437
  · exact u13438

def r31369 : Route 9 := (fun mask => (mask,id))

def c31369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31369 : Upper (D 6) (R 6) [10,36,129,80,260] 13 := by
  apply FastRouting.sound _ _ [10,36,129,80,260] 13 (by decide) (choices 1) [1,2,64] r31369 c31369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13439
  · exact u13440
  · exact u13441

def r31370 : Route 9 := (fun mask => (mask,id))

def c31370 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31370 : Upper (D 6) (R 6) [10,36,129,80,288] 13 := by
  apply FastRouting.sound _ _ [10,36,129,80,288] 13 (by decide) (choices 1) [1,2,4,64] r31370 c31370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13442
  · exact u13443
  · exact u13444
  · exact u13445

def b31371 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 38 133 88 336 39 103 167 295), lower := (rows 11 38 133 88 336 32 64 128 256), losses := [] }

theorem u31371 : Upper (D 6) (R 6) [10,36,129,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31372 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 38 133 104 19 372 340 468 340), lower := (rows 11 38 133 104 19 32 64 128 256), losses := [] }

theorem u31372 : Upper (D 6) (R 6) [10,36,129,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31373 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 38 133 104 21 370 338 466 338), lower := (rows 11 38 133 104 21 32 64 128 256), losses := [] }

theorem u31373 : Upper (D 6) (R 6) [10,36,129,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31374 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 133 104 22 369 337 465 337), lower := (rows 11 38 133 104 22 32 64 128 256), losses := [] }

theorem u31374 : Upper (D 6) (R 6) [10,36,129,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31375 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 38 133 104 81 310 342 406 278), lower := (rows 11 38 133 104 81 32 64 128 256), losses := [] }

theorem u31375 : Upper (D 6) (R 6) [10,36,129,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31376 : Route 9 := (fun mask => (mask,id))

def c31376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31376 : Upper (D 6) (R 6) [10,36,129,96,66] 13 := by
  apply FastRouting.sound _ _ [10,36,129,96,66] 13 (by decide) (choices 1) [1,4,16,256] r31376 c31376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13446
  · exact u13447
  · exact u13448
  · exact u13449

def r31377 : Route 9 := (fun mask => (mask,id))

def c31377 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31377 : Upper (D 6) (R 6) [10,36,129,96,68] 13 := by
  apply FastRouting.sound _ _ [10,36,129,96,68] 13 (by decide) (choices 1) [1,2,16,256] r31377 c31377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13450
  · exact u13451
  · exact u13452
  · exact u13453

def r31378 : Route 9 := (fun mask => (mask,id))

def c31378 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31378 : Upper (D 6) (R 6) [10,36,129,96,257] 13 := by
  apply FastRouting.sound _ _ [10,36,129,96,257] 13 (by decide) (choices 1) [2,4,16,64] r31378 c31378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13454
  · exact u13455
  · exact u13456
  · exact u13457

def r31379 : Route 9 := (fun mask => (mask,id))

def c31379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31379 : Upper (D 6) (R 6) [10,36,129,96,258] 13 := by
  apply FastRouting.sound _ _ [10,36,129,96,258] 13 (by decide) (choices 1) [1,4,16,64] r31379 c31379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13458
  · exact u13459
  · exact u13460
  · exact u13461

#print axioms u31379
end Delivery.IrregularNine14.P06
