import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0089
import IrregularNine14P01C0090

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8460 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 305 67 14 74 180 180 244 180 436), lower := (rows 305 67 14 74 16 32 64 128 256), losses := [] }

theorem u8460 : Upper (D 1) (R 1) [304,65,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8460
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8461 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 305 67 14 76 178 178 242 178 434), lower := (rows 305 67 14 76 16 32 64 128 256), losses := [] }

theorem u8461 : Upper (D 1) (R 1) [304,65,10,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8461
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8462 : PairBound 9 := { available := 166, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 67 14 88 182 166 230 166 422), lower := (rows 305 67 14 88 16 32 64 128 256), losses := [] }

theorem u8462 : Upper (D 1) (R 1) [304,65,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8462
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8463 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 67 14 138 244 244 244 244 500), lower := (rows 305 67 14 138 16 32 64 128 256), losses := [] }

theorem u8463 : Upper (D 1) (R 1) [304,65,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8463
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8464 : Route 9 := (fun mask => (mask,id))

def c8464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8464 : Upper (D 1) (R 1) [304,65,10,132] 13 := by
  apply FastRouting.sound _ _ [304,65,10,132] 13 (by decide) (choices 1) [2,32,64,128] r8464 c8464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5359
  · exact u5360
  · exact u5361
  · exact u5362

def r8465 : Route 9 := (fun mask => (mask,id))

def c8465 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u8465 : Upper (D 1) (R 1) [304,65,10,144] 13 := by
  apply FastRouting.sound _ _ [304,65,10,144] 13 (by decide) (choices 1) [2,4,32,64,128] r8465 c8465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5363
  · exact u5364
  · exact u5365
  · exact u5366
  · exact u5367

def b8466 : PairBound 9 := { available := 182, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 67 14 200 182 182 246 182 438), lower := (rows 305 67 14 200 16 32 64 128 256), losses := [] }

theorem u8466 : Upper (D 1) (R 1) [304,65,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8466
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8467 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 67 22 44 218 234 202 202 458), lower := (rows 305 67 22 44 16 32 64 128 256), losses := [] }

theorem u8467 : Upper (D 1) (R 1) [304,65,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8467
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8468 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 67 22 76 186 170 234 170 426), lower := (rows 305 67 22 76 16 32 64 128 256), losses := [] }

theorem u8468 : Upper (D 1) (R 1) [304,65,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8468
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8469 : PairBound 9 := { available := 142, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 67 22 104 158 174 206 142 398), lower := (rows 305 67 22 104 16 32 64 128 256), losses := [] }

theorem u8469 : Upper (D 1) (R 1) [304,65,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8469
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8470 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 67 22 138 252 236 236 236 492), lower := (rows 305 67 22 138 16 32 64 128 256), losses := [] }

theorem u8470 : Upper (D 1) (R 1) [304,65,18,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8470
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8471 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 67 22 140 250 234 234 234 490), lower := (rows 305 67 22 140 16 32 64 128 256), losses := [] }

theorem u8471 : Upper (D 1) (R 1) [304,65,18,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8471
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8472 : PairBound 9 := { available := 206, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 67 22 168 222 238 206 206 462), lower := (rows 305 67 22 168 16 32 64 128 256), losses := [] }

theorem u8472 : Upper (D 1) (R 1) [304,65,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8472
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8473 : PairBound 9 := { available := 174, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 67 22 200 190 174 238 174 430), lower := (rows 305 67 22 200 16 32 64 128 256), losses := [] }

theorem u8473 : Upper (D 1) (R 1) [304,65,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8473
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8474 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 28 44 210 226 194 194 450), lower := (rows 305 67 28 44 16 32 64 128 256), losses := [] }

theorem u8474 : Upper (D 1) (R 1) [304,65,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8474
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8475 : PairBound 9 := { available := 166, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 67 28 74 182 166 230 166 422), lower := (rows 305 67 28 74 16 32 64 128 256), losses := [] }

theorem u8475 : Upper (D 1) (R 1) [304,65,24,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8475
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8476 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 305 67 28 76 178 162 226 162 418), lower := (rows 305 67 28 76 16 32 64 128 256), losses := [] }

theorem u8476 : Upper (D 1) (R 1) [304,65,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8476
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8477 : Route 9 := (fun mask => (mask,id))

def c8477 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8477 : Upper (D 1) (R 1) [304,65,24,96] 13 := by
  apply FastRouting.sound _ _ [304,65,24,96] 13 (by decide) (choices 1) [2,4,128] r8477 c8477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5368
  · exact u5369
  · exact u5370

def r8478 : Route 9 := (fun mask => (mask,id))

def c8478 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u8478 : Upper (D 1) (R 1) [304,65,24,130] 13 := by
  apply FastRouting.sound _ _ [304,65,24,130] 13 (by decide) (choices 1) [2,4,32,64,128] r8478 c8478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5371
  · exact u5372
  · exact u5373
  · exact u5374
  · exact u5375

def b8479 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 305 67 28 140 242 226 226 226 482), lower := (rows 305 67 28 140 16 32 64 128 256), losses := [] }

theorem u8479 : Upper (D 1) (R 1) [304,65,24,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8479
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8480 : Route 9 := (fun mask => (mask,id))

def c8480 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8480 : Upper (D 1) (R 1) [304,65,24,160] 13 := by
  apply FastRouting.sound _ _ [304,65,24,160] 13 (by decide) (choices 1) [2,4,64,128] r8480 c8480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5376
  · exact u5377
  · exact u5378
  · exact u5379

def r8481 : Route 9 := (fun mask => (mask,id))

def c8481 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8481 : Upper (D 1) (R 1) [304,65,24,192] 13 := by
  apply FastRouting.sound _ _ [304,65,24,192] 13 (by decide) (choices 1) [2,4,32,128] r8481 c8481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5380
  · exact u5381
  · exact u5382
  · exact u5383

def b8482 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 52 76 154 170 202 138 394), lower := (rows 305 67 52 76 16 32 64 128 256), losses := [] }

theorem u8482 : Upper (D 1) (R 1) [304,65,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8482
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8483 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 52 138 222 238 206 206 462), lower := (rows 305 67 52 138 16 32 64 128 256), losses := [] }

theorem u8483 : Upper (D 1) (R 1) [304,65,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8483
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8484 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 52 140 218 234 202 202 458), lower := (rows 305 67 52 140 16 32 64 128 256), losses := [] }

theorem u8484 : Upper (D 1) (R 1) [304,65,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8484
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8485 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 52 200 158 174 206 142 398), lower := (rows 305 67 52 200 16 32 64 128 256), losses := [] }

theorem u8485 : Upper (D 1) (R 1) [304,65,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8485
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8486 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 67 70 138 188 188 252 188 444), lower := (rows 305 67 70 138 16 32 64 128 256), losses := [] }

theorem u8486 : Upper (D 1) (R 1) [304,65,66,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8486
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8487 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 67 70 140 186 186 250 186 442), lower := (rows 305 67 70 140 16 32 64 128 256), losses := [] }

theorem u8487 : Upper (D 1) (R 1) [304,65,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8487
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8488 : PairBound 9 := { available := 174, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 67 70 152 190 174 238 174 430), lower := (rows 305 67 70 152 16 32 64 128 256), losses := [] }

theorem u8488 : Upper (D 1) (R 1) [304,65,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8488
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8489 : Route 9 := (fun mask => (mask,id))

def c8489 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8489 : Upper (D 1) (R 1) [304,65,72,130] 13 := by
  apply FastRouting.sound _ _ [304,65,72,130] 13 (by decide) (choices 1) [2,4,32,128] r8489 c8489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5384
  · exact u5385
  · exact u5386
  · exact u5387

def b8490 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 67 76 140 178 178 242 178 434), lower := (rows 305 67 76 140 16 32 64 128 256), losses := [] }

theorem u8490 : Upper (D 1) (R 1) [304,65,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8490
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8491 : Route 9 := (fun mask => (mask,id))

def c8491 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8491 : Upper (D 1) (R 1) [304,65,72,144] 13 := by
  apply FastRouting.sound _ _ [304,65,72,144] 13 (by decide) (choices 1) [2,4,32,128] r8491 c8491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5388
  · exact u5389
  · exact u5390
  · exact u5391

def r8492 : Route 9 := (fun mask => (mask,id))

def c8492 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u8492 : Upper (D 1) (R 1) [304,65,80,130] 13 := by
  apply FastRouting.sound _ _ [304,65,80,130] 13 (by decide) (choices 1) [2,4,8,32,128] r8492 c8492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5392
  · exact u5393
  · exact u5394
  · exact u5395
  · exact u5396

def r8493 : Route 9 := (fun mask => (mask,id))

def c8493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8493 : Upper (D 1) (R 1) [304,65,80,132] 13 := by
  apply FastRouting.sound _ _ [304,65,80,132] 13 (by decide) (choices 1) [2,8,32,128] r8493 c8493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5397
  · exact u5398
  · exact u5399
  · exact u5400

def r8494 : Route 9 := (fun mask => (mask,id))

def c8494 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8494 : Upper (D 1) (R 1) [304,65,80,160] 13 := by
  apply FastRouting.sound _ _ [304,65,80,160] 13 (by decide) (choices 1) [2,4,8,128] r8494 c8494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5401
  · exact u5402
  · exact u5403
  · exact u5404

def b8495 : PairBound 9 := { available := 124, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 67 134 138 124 124 124 252 380), lower := (rows 305 67 134 138 16 32 64 128 256), losses := [] }

theorem u8495 : Upper (D 1) (R 1) [304,65,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8495
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8496 : PairBound 9 := { available := 122, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 67 134 140 122 122 122 250 378), lower := (rows 305 67 134 140 16 32 64 128 256), losses := [] }

theorem u8496 : Upper (D 1) (R 1) [304,65,130,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8496
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8497 : Route 9 := (fun mask => (mask,id))

def c8497 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u8497 : Upper (D 1) (R 1) [304,65,130,144] 13 := by
  apply FastRouting.sound _ _ [304,65,130,144] 13 (by decide) (choices 1) [2,4,8,32,64] r8497 c8497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5405
  · exact u5406
  · exact u5407
  · exact u5408
  · exact u5409

def r8498 : Route 9 := (fun mask => (mask,id))

def c8498 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8498 : Upper (D 1) (R 1) [304,65,130,192] 13 := by
  apply FastRouting.sound _ _ [304,65,130,192] 13 (by decide) (choices 1) [2,4,8,32] r8498 c8498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5410
  · exact u5411
  · exact u5412
  · exact u5413

def b8499 : PairBound 9 := { available := 114, camps := [{ cop := 7, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 140 140 114 114 114 242 370), lower := (rows 305 67 140 140 16 32 64 128 256), losses := [] }

theorem u8499 : Upper (D 1) (R 1) [304,65,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8499
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8500 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 140 152 118 102 102 230 358), lower := (rows 305 67 140 152 16 32 64 128 256), losses := [] }

theorem u8500 : Upper (D 1) (R 1) [304,65,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8500
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8501 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 140 200 54 54 118 182 310), lower := (rows 305 67 140 200 16 32 64 128 256), losses := [] }

theorem u8501 : Upper (D 1) (R 1) [304,65,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8501
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8502 : Route 9 := (fun mask => (mask,id))

def c8502 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8502 : Upper (D 1) (R 1) [304,65,144,160] 13 := by
  apply FastRouting.sound _ _ [304,65,144,160] 13 (by decide) (choices 1) [2,4,8,64] r8502 c8502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5414
  · exact u5415
  · exact u5416
  · exact u5417

def r8503 : Route 9 := (fun mask => (mask,id))

def c8503 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8503 : Upper (D 1) (R 1) [304,65,144,192] 13 := by
  apply FastRouting.sound _ _ [304,65,144,192] 13 (by decide) (choices 1) [2,4,8,32] r8503 c8503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5418
  · exact u5419
  · exact u5420
  · exact u5421

def b8504 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 7 26 248 232 232 232 488), lower := (rows 305 70 7 26 16 32 64 128 256), losses := [] }

theorem u8504 : Upper (D 1) (R 1) [304,68,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8504
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8505 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 70 7 56 218 234 202 202 458), lower := (rows 305 70 7 56 16 32 64 128 256), losses := [] }

theorem u8505 : Upper (D 1) (R 1) [304,68,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8505
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8506 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 7 74 184 184 248 184 440), lower := (rows 305 70 7 74 16 32 64 128 256), losses := [] }

theorem u8506 : Upper (D 1) (R 1) [304,68,3,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8506
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8507 : Route 9 := (fun mask => (mask,id))

def c8507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8507 : Upper (D 1) (R 1) [304,68,3,80] 13 := by
  apply FastRouting.sound _ _ [304,68,3,80] 13 (by decide) (choices 1) [2,8,32,128] r8507 c8507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5422
  · exact u5423
  · exact u5424
  · exact u5425

def b8508 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 369, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 7 138 248 248 248 248 504), lower := (rows 305 70 7 138 16 32 64 128 256), losses := [] }

theorem u8508 : Upper (D 1) (R 1) [304,68,3,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8508
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8509 : Route 9 := (fun mask => (mask,id))

def c8509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u8509 : Upper (D 1) (R 1) [304,68,3,144] 13 := by
  apply FastRouting.sound _ _ [304,68,3,144] 13 (by decide) (choices 1) [2,8,32,64,128] r8509 c8509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5426
  · exact u5427
  · exact u5428
  · exact u5429
  · exact u5430

def r8510 : Route 9 := (fun mask => (mask,id))

def c8510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8510 : Upper (D 1) (R 1) [304,68,3,192] 13 := by
  apply FastRouting.sound _ _ [304,68,3,192] 13 (by decide) (choices 1) [2,8,32,128] r8510 c8510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5431
  · exact u5432
  · exact u5433
  · exact u5434

def b8511 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 13 26 242 226 226 226 482), lower := (rows 305 70 13 26 16 32 64 128 256), losses := [] }

theorem u8511 : Upper (D 1) (R 1) [304,68,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8511
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8512 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 13 56 210 226 194 194 450), lower := (rows 305 70 13 56 16 32 64 128 256), losses := [] }

theorem u8512 : Upper (D 1) (R 1) [304,68,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8512
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8513 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 13 74 178 178 242 178 434), lower := (rows 305 70 13 74 16 32 64 128 256), losses := [] }

theorem u8513 : Upper (D 1) (R 1) [304,68,9,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8513
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8514 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 70 13 88 178 162 226 162 418), lower := (rows 305 70 13 88 16 32 64 128 256), losses := [] }

theorem u8514 : Upper (D 1) (R 1) [304,68,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8514
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8515 : Route 9 := (fun mask => (mask,id))

def c8515 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8515 : Upper (D 1) (R 1) [304,68,9,130] 13 := by
  apply FastRouting.sound _ _ [304,68,9,130] 13 (by decide) (choices 1) [2,32,64,128] r8515 c8515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5435
  · exact u5436
  · exact u5437
  · exact u5438

def b8516 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 13 152 242 226 226 226 482), lower := (rows 305 70 13 152 16 32 64 128 256), losses := [] }

theorem u8516 : Upper (D 1) (R 1) [304,68,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8516
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8517 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 70 13 200 178 178 242 178 434), lower := (rows 305 70 13 200 16 32 64 128 256), losses := [] }

theorem u8517 : Upper (D 1) (R 1) [304,68,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8517
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8518 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 70 14 11 240 240 240 240 496), lower := (rows 305 70 14 11 16 32 64 128 256), losses := [] }

theorem u8518 : Upper (D 1) (R 1) [304,68,10,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8518
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8519 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 70 14 25 242 226 226 226 482), lower := (rows 305 70 14 25 16 32 64 128 256), losses := [] }

theorem u8519 : Upper (D 1) (R 1) [304,68,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8519
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u8519
end Delivery.IrregularNine14.P01
