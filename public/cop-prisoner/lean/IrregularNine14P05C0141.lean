import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0082
import IrregularNine14P05C0083

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8460 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 17, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 70 134 296 25 47 79 143 271), lower := (rows 49 70 134 296 25 32 64 128 256), losses := [] }

theorem u8460 : Upper (D 5) (R 5) [48,68,130,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8460
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8461 : Route 9 := (fun mask => (mask,id))

def c8461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8461 : Upper (D 5) (R 5) [48,68,130,288,10] 13 := by
  apply FastRouting.sound _ _ [48,68,130,288,10] 13 (by decide) (choices 1) [1,4,8] r8461 c8461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4969
  · exact u4970
  · exact u4971

def r8462 : Route 9 := (fun mask => (mask,id))

def c8462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8462 : Upper (D 5) (R 5) [48,68,136,258,3] 13 := by
  apply FastRouting.sound _ _ [48,68,136,258,3] 13 (by decide) (choices 1) [1,4,8] r8462 c8462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4972
  · exact u4973
  · exact u4974

def b8463 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 49 70 140 266 22 41 105 169 297), lower := (rows 49 70 140 266 22 32 64 128 256), losses := [] }

theorem u8463 : Upper (D 5) (R 5) [48,68,136,258,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8463
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8464 : PairBound 9 := { available := 15, camps := [{ cop := 5, region := 17, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 70 140 266 49 47 79 143 271), lower := (rows 49 70 140 266 49 32 64 128 256), losses := [] }

theorem u8464 : Upper (D 5) (R 5) [48,68,136,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8464
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8465 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 70 140 266 50 45 77 141 269), lower := (rows 49 70 140 266 50 32 64 128 256), losses := [] }

theorem u8465 : Upper (D 5) (R 5) [48,68,136,258,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8465
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8466 : Route 9 := (fun mask => (mask,id))

def c8466 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8466 : Upper (D 5) (R 5) [48,68,136,288,3] 13 := by
  apply FastRouting.sound _ _ [48,68,136,288,3] 13 (by decide) (choices 1) [1,2,4,8] r8466 c8466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4975
  · exact u4976
  · exact u4977
  · exact u4978

def r8467 : Route 9 := (fun mask => (mask,id))

def c8467 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8467 : Upper (D 5) (R 5) [48,68,136,288,5] 13 := by
  apply FastRouting.sound _ _ [48,68,136,288,5] 13 (by decide) (choices 1) [1,2,8] r8467 c8467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4979
  · exact u4980
  · exact u4981

def b8468 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 49 70 140 296 22 43 75 139 267), lower := (rows 49 70 140 296 22 32 64 128 256), losses := [] }

theorem u8468 : Upper (D 5) (R 5) [48,68,136,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8468
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8469 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 17, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 70 140 296 25 39 71 135 263), lower := (rows 49 70 140 296 25 32 64 128 256), losses := [] }

theorem u8469 : Upper (D 5) (R 5) [48,68,136,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8469
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8470 : Route 9 := (fun mask => (mask,id))

def c8470 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8470 : Upper (D 5) (R 5) [48,68,136,288,10] 13 := by
  apply FastRouting.sound _ _ [48,68,136,288,10] 13 (by decide) (choices 1) [1,2,4] r8470 c8470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4982
  · exact u4983
  · exact u4984

def b8471 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 49 70 140 296 28 35 67 131 259), lower := (rows 49 70 140 296 28 32 64 128 256), losses := [] }

theorem u8471 : Upper (D 5) (R 5) [48,68,136,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8471
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8472 : Route 9 := (fun mask => (mask,id))

def c8472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8472 : Upper (D 5) (R 5) [48,68,160,260,3] 13 := by
  apply FastRouting.sound _ _ [48,68,160,260,3] 13 (by decide) (choices 1) [1,2,8] r8472 c8472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4985
  · exact u4986
  · exact u4987

theorem m8473_8 : Upper (D 5) (R 5) [48,68,160,260,10,8] 13 :=
  permutation_upper _ _ _ [48,68,160,260,10,2] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4989

def r8473 : Route 9 := (fun mask => (mask,id))

def c8473 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8473 : Upper (D 5) (R 5) [48,68,160,260,10] 13 := by
  apply FastRouting.sound _ _ [48,68,160,260,10] 13 (by decide) (choices 1) [1,2,8] r8473 c8473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4988
  · exact u4989
  · exact m8473_8

def b8474 : PairBound 9 := { available := 490, camps := [{ cop := 1, region := 504, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 7 13 56 506 490 490 490 490), lower := (rows 7 7 13 56 16 32 64 128 256), losses := [] }

theorem u8474 : Upper (D 5) (R 5) [6,5,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8474
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8475 : PairBound 9 := { available := 426, camps := [{ cop := 1, region := 504, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 7 13 88 442 426 490 426 426), lower := (rows 7 7 13 88 16 32 64 128 256), losses := [] }

theorem u8475 : Upper (D 5) (R 5) [6,5,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8475
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8476 : PairBound 9 := { available := 442, camps := [{ cop := 1, region := 504, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 7 13 104 442 442 506 442 442), lower := (rows 7 7 13 104 16 32 64 128 256), losses := [] }

theorem u8476 : Upper (D 5) (R 5) [6,5,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8476
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8477 : PairBound 9 := { available := 314, camps := [{ cop := 1, region := 504, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 7 13 200 314 314 378 442 314), lower := (rows 7 7 13 200 16 32 64 128 256), losses := [] }

theorem u8477 : Upper (D 5) (R 5) [6,5,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8477
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8478 : PairBound 9 := { available := 426, camps := [{ cop := 4, region := 7, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 21 104 442 426 490 426 426), lower := (rows 7 7 21 104 16 32 64 128 256), losses := [] }

theorem u8478 : Upper (D 5) (R 5) [6,5,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8478
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8479 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 7, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 21 200 314 298 362 426 298), lower := (rows 7 7 21 200 16 32 64 128 256), losses := [] }

theorem u8479 : Upper (D 5) (R 5) [6,5,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8479
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8480 : PairBound 9 := { available := 490, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 28 41 506 490 490 490 490), lower := (rows 7 7 28 41 16 32 64 128 256), losses := [] }

theorem u8480 : Upper (D 5) (R 5) [6,5,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8480
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8481 : PairBound 9 := { available := 426, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 28 73 442 426 490 426 426), lower := (rows 7 7 28 73 16 32 64 128 256), losses := [] }

theorem u8481 : Upper (D 5) (R 5) [6,5,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8481
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8482 : PairBound 9 := { available := 427, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 28 104 443 427 491 427 427), lower := (rows 7 7 28 104 16 32 64 128 256), losses := [] }

theorem u8482 : Upper (D 5) (R 5) [6,5,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8482
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8483 : PairBound 9 := { available := 299, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 28 200 315 299 363 427 299), lower := (rows 7 7 28 200 16 32 64 128 256), losses := [] }

theorem u8483 : Upper (D 5) (R 5) [6,5,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8483
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8484 : PairBound 9 := { available := 458, camps := [{ cop := 1, region := 504, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 7 37 56 474 490 458 458 458), lower := (rows 7 7 37 56 16 32 64 128 256), losses := [] }

theorem u8484 : Upper (D 5) (R 5) [6,5,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8484
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8485 : PairBound 9 := { available := 426, camps := [{ cop := 1, region := 504, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 7 37 88 442 426 490 426 426), lower := (rows 7 7 37 88 16 32 64 128 256), losses := [] }

theorem u8485 : Upper (D 5) (R 5) [6,5,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8485
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8486 : PairBound 9 := { available := 410, camps := [{ cop := 1, region := 504, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 7 37 104 410 442 474 410 410), lower := (rows 7 7 37 104 16 32 64 128 256), losses := [] }

theorem u8486 : Upper (D 5) (R 5) [6,5,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8486
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8487 : PairBound 9 := { available := 314, camps := [{ cop := 1, region := 504, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 7 37 200 314 314 378 442 314), lower := (rows 7 7 37 200 16 32 64 128 256), losses := [] }

theorem u8487 : Upper (D 5) (R 5) [6,5,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8487
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8488 : PairBound 9 := { available := 490, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 44 25 506 490 490 490 490), lower := (rows 7 7 44 25 16 32 64 128 256), losses := [] }

theorem u8488 : Upper (D 5) (R 5) [6,5,40,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8488
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8489 : PairBound 9 := { available := 442, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 44 73 442 442 506 442 442), lower := (rows 7 7 44 73 16 32 64 128 256), losses := [] }

theorem u8489 : Upper (D 5) (R 5) [6,5,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8489
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8490 : PairBound 9 := { available := 427, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 44 88 443 427 491 427 427), lower := (rows 7 7 44 88 16 32 64 128 256), losses := [] }

theorem u8490 : Upper (D 5) (R 5) [6,5,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8490
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8491 : PairBound 9 := { available := 315, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 44 200 315 315 379 443 315), lower := (rows 7 7 44 200 16 32 64 128 256), losses := [] }

theorem u8491 : Upper (D 5) (R 5) [6,5,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8491
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8492 : PairBound 9 := { available := 458, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 52 41 474 490 458 458 458), lower := (rows 7 7 52 41 16 32 64 128 256), losses := [] }

theorem u8492 : Upper (D 5) (R 5) [6,5,48,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8492
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8493 : PairBound 9 := { available := 426, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 52 73 442 426 490 426 426), lower := (rows 7 7 52 73 16 32 64 128 256), losses := [] }

theorem u8493 : Upper (D 5) (R 5) [6,5,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8493
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8494 : PairBound 9 := { available := 395, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 52 104 411 427 459 395 395), lower := (rows 7 7 52 104 16 32 64 128 256), losses := [] }

theorem u8494 : Upper (D 5) (R 5) [6,5,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8494
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8495 : PairBound 9 := { available := 299, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 52 200 315 299 363 427 299), lower := (rows 7 7 52 200 16 32 64 128 256), losses := [] }

theorem u8495 : Upper (D 5) (R 5) [6,5,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8495
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8496 : PairBound 9 := { available := 426, camps := [{ cop := 6, region := 7, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 69 56 442 426 490 426 426), lower := (rows 7 7 69 56 16 32 64 128 256), losses := [] }

theorem u8496 : Upper (D 5) (R 5) [6,5,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8496
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8497 : PairBound 9 := { available := 298, camps := [{ cop := 6, region := 7, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 69 152 314 298 362 426 298), lower := (rows 7 7 69 152 16 32 64 128 256), losses := [] }

theorem u8497 : Upper (D 5) (R 5) [6,5,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8497
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8498 : PairBound 9 := { available := 314, camps := [{ cop := 6, region := 7, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 69 168 314 314 378 442 314), lower := (rows 7 7 69 168 16 32 64 128 256), losses := [] }

theorem u8498 : Upper (D 5) (R 5) [6,5,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8498
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8499 : PairBound 9 := { available := 58, camps := [{ cop := 6, region := 7, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 69 392 58 58 122 186 314), lower := (rows 7 7 69 392 16 32 64 128 256), losses := [] }

theorem u8499 : Upper (D 5) (R 5) [6,5,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8499
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8500 : PairBound 9 := { available := 426, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 76 25 442 426 490 426 426), lower := (rows 7 7 76 25 16 32 64 128 256), losses := [] }

theorem u8500 : Upper (D 5) (R 5) [6,5,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8500
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8501 : PairBound 9 := { available := 442, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 76 41 442 442 506 442 442), lower := (rows 7 7 76 41 16 32 64 128 256), losses := [] }

theorem u8501 : Upper (D 5) (R 5) [6,5,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8501
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8502 : PairBound 9 := { available := 427, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 76 56 443 427 491 427 427), lower := (rows 7 7 76 56 16 32 64 128 256), losses := [] }

theorem u8502 : Upper (D 5) (R 5) [6,5,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8502
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8503 : PairBound 9 := { available := 314, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 76 137 314 314 378 442 314), lower := (rows 7 7 76 137 16 32 64 128 256), losses := [] }

theorem u8503 : Upper (D 5) (R 5) [6,5,72,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8503
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8504 : PairBound 9 := { available := 299, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 76 152 315 299 363 427 299), lower := (rows 7 7 76 152 16 32 64 128 256), losses := [] }

theorem u8504 : Upper (D 5) (R 5) [6,5,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8504
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8505 : PairBound 9 := { available := 315, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 76 168 315 315 379 443 315), lower := (rows 7 7 76 168 16 32 64 128 256), losses := [] }

theorem u8505 : Upper (D 5) (R 5) [6,5,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8505
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8506 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 76 392 59 59 123 187 315), lower := (rows 7 7 76 392 16 32 64 128 256), losses := [] }

theorem u8506 : Upper (D 5) (R 5) [6,5,72,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8506
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8507 : PairBound 9 := { available := 426, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 84 41 442 426 490 426 426), lower := (rows 7 7 84 41 16 32 64 128 256), losses := [] }

theorem u8507 : Upper (D 5) (R 5) [6,5,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8507
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8508 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 84 137 314 298 362 426 298), lower := (rows 7 7 84 137 16 32 64 128 256), losses := [] }

theorem u8508 : Upper (D 5) (R 5) [6,5,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8508
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8509 : PairBound 9 := { available := 299, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 84 168 315 299 363 427 299), lower := (rows 7 7 84 168 16 32 64 128 256), losses := [] }

theorem u8509 : Upper (D 5) (R 5) [6,5,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8509
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8510 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 84 392 59 43 107 171 299), lower := (rows 7 7 84 392 16 32 64 128 256), losses := [] }

theorem u8510 : Upper (D 5) (R 5) [6,5,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8510
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8511 : PairBound 9 := { available := 426, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 100 25 442 426 490 426 426), lower := (rows 7 7 100 25 16 32 64 128 256), losses := [] }

theorem u8511 : Upper (D 5) (R 5) [6,5,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8511
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8512 : PairBound 9 := { available := 410, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 100 41 410 442 474 410 410), lower := (rows 7 7 100 41 16 32 64 128 256), losses := [] }

theorem u8512 : Upper (D 5) (R 5) [6,5,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8512
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8513 : PairBound 9 := { available := 395, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 100 56 411 427 459 395 395), lower := (rows 7 7 100 56 16 32 64 128 256), losses := [] }

theorem u8513 : Upper (D 5) (R 5) [6,5,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8513
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8514 : PairBound 9 := { available := 314, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 100 137 314 314 378 442 314), lower := (rows 7 7 100 137 16 32 64 128 256), losses := [] }

theorem u8514 : Upper (D 5) (R 5) [6,5,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8514
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8515 : PairBound 9 := { available := 299, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 100 152 315 299 363 427 299), lower := (rows 7 7 100 152 16 32 64 128 256), losses := [] }

theorem u8515 : Upper (D 5) (R 5) [6,5,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8515
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8516 : PairBound 9 := { available := 283, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 100 168 283 315 347 411 283), lower := (rows 7 7 100 168 16 32 64 128 256), losses := [] }

theorem u8516 : Upper (D 5) (R 5) [6,5,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8516
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8517 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 100 392 59 59 123 187 315), lower := (rows 7 7 100 392 16 32 64 128 256), losses := [] }

theorem u8517 : Upper (D 5) (R 5) [6,5,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8517
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8518 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 196 25 314 298 362 426 298), lower := (rows 7 7 196 25 16 32 64 128 256), losses := [] }

theorem u8518 : Upper (D 5) (R 5) [6,5,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8518
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8519 : PairBound 9 := { available := 314, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 196 41 314 314 378 442 314), lower := (rows 7 7 196 41 16 32 64 128 256), losses := [] }

theorem u8519 : Upper (D 5) (R 5) [6,5,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8519
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8519
end Delivery.IrregularNine14.P05
