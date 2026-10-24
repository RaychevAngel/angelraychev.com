import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0090
import IrregularNine14P01C0091
import IrregularNine14P01C0092

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8520 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 70 14 26 241 225 225 225 481), lower := (rows 305 70 14 26 16 32 64 128 256), losses := [] }

theorem u8520 : Upper (D 1) (R 1) [304,68,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8520
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8521 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 70 14 56 211 227 195 195 451), lower := (rows 305 70 14 56 16 32 64 128 256), losses := [] }

theorem u8521 : Upper (D 1) (R 1) [304,68,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8521
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8522 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 14 73 178 178 242 178 434), lower := (rows 305 70 14 73 16 32 64 128 256), losses := [] }

theorem u8522 : Upper (D 1) (R 1) [304,68,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8522
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8523 : PairBound 9 := { available := 177, camps := [{ cop := 6, region := 14, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 14 74 177 177 241 177 433), lower := (rows 305 70 14 74 16 32 64 128 256), losses := [] }

theorem u8523 : Upper (D 1) (R 1) [304,68,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8523
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8524 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 14 88 179 163 227 163 419), lower := (rows 305 70 14 88 16 32 64 128 256), losses := [] }

theorem u8524 : Upper (D 1) (R 1) [304,68,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8524
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8525 : Route 9 := (fun mask => (mask,id))

def c8525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8525 : Upper (D 1) (R 1) [304,68,10,129] 13 := by
  apply FastRouting.sound _ _ [304,68,10,129] 13 (by decide) (choices 1) [2,32,64,128] r8525 c8525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5439
  · exact u5440
  · exact u5441
  · exact u5442

def b8526 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 70 14 138 241 241 241 241 497), lower := (rows 305 70 14 138 16 32 64 128 256), losses := [] }

theorem u8526 : Upper (D 1) (R 1) [304,68,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8526
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8527 : Route 9 := (fun mask => (mask,id))

def c8527 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8527 : Upper (D 1) (R 1) [304,68,10,144] 13 := by
  apply FastRouting.sound _ _ [304,68,10,144] 13 (by decide) (choices 1) [1,2,32,64,128] r8527 c8527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5443
  · exact u5444
  · exact u5445
  · exact u5446
  · exact u5447

def b8528 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 14 200 179 179 243 179 435), lower := (rows 305 70 14 200 16 32 64 128 256), losses := [] }

theorem u8528 : Upper (D 1) (R 1) [304,68,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8528
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8529 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 22 11 248 232 232 232 488), lower := (rows 305 70 22 11 16 32 64 128 256), losses := [] }

theorem u8529 : Upper (D 1) (R 1) [304,68,18,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8529
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8530 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 70 22 41 218 234 202 202 458), lower := (rows 305 70 22 41 16 32 64 128 256), losses := [] }

theorem u8530 : Upper (D 1) (R 1) [304,68,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8530
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8531 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 22 42 217 233 201 201 457), lower := (rows 305 70 22 42 16 32 64 128 256), losses := [] }

theorem u8531 : Upper (D 1) (R 1) [304,68,18,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8531
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8532 : Route 9 := (fun mask => (mask,id))

def c8532 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8532 : Upper (D 1) (R 1) [304,68,18,65] 13 := by
  apply FastRouting.sound _ _ [304,68,18,65] 13 (by decide) (choices 1) [2,8,32,128] r8532 c8532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5448
  · exact u5449
  · exact u5450
  · exact u5451

def b8533 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 22 74 185 169 233 169 425), lower := (rows 305 70 22 74 16 32 64 128 256), losses := [] }

theorem u8533 : Upper (D 1) (R 1) [304,68,18,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8533
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8534 : Route 9 := (fun mask => (mask,id))

def c8534 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8534 : Upper (D 1) (R 1) [304,68,18,96] 13 := by
  apply FastRouting.sound _ _ [304,68,18,96] 13 (by decide) (choices 1) [1,2,8,128] r8534 c8534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5452
  · exact u5453
  · exact u5454
  · exact u5455

def r8535 : Route 9 := (fun mask => (mask,id))

def c8535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u8535 : Upper (D 1) (R 1) [304,68,18,129] 13 := by
  apply FastRouting.sound _ _ [304,68,18,129] 13 (by decide) (choices 1) [2,8,32,64,128] r8535 c8535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5456
  · exact u5457
  · exact u5458
  · exact u5459
  · exact u5460

def b8536 : PairBound 9 := { available := 233, camps := [{ cop := 3, region := 369, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 22 138 249 233 233 233 489), lower := (rows 305 70 22 138 16 32 64 128 256), losses := [] }

theorem u8536 : Upper (D 1) (R 1) [304,68,18,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8536
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8537 : Route 9 := (fun mask => (mask,id))

def c8537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8537 : Upper (D 1) (R 1) [304,68,18,160] 13 := by
  apply FastRouting.sound _ _ [304,68,18,160] 13 (by decide) (choices 1) [1,2,8,64,128] r8537 c8537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5461
  · exact u5462
  · exact u5463
  · exact u5464
  · exact u5465

def r8538 : Route 9 := (fun mask => (mask,id))

def c8538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8538 : Upper (D 1) (R 1) [304,68,18,192] 13 := by
  apply FastRouting.sound _ _ [304,68,18,192] 13 (by decide) (choices 1) [1,2,8,32,128] r8538 c8538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5466
  · exact u5467
  · exact u5468
  · exact u5469
  · exact u5470

def b8539 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 28 11 242 226 226 226 482), lower := (rows 305 70 28 11 16 32 64 128 256), losses := [] }

theorem u8539 : Upper (D 1) (R 1) [304,68,24,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8539
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8540 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 28 41 210 226 194 194 450), lower := (rows 305 70 28 41 16 32 64 128 256), losses := [] }

theorem u8540 : Upper (D 1) (R 1) [304,68,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8540
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8541 : Route 9 := (fun mask => (mask,id))

def c8541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8541 : Upper (D 1) (R 1) [304,68,24,34] 13 := by
  apply FastRouting.sound _ _ [304,68,24,34] 13 (by decide) (choices 1) [1,2,64,128] r8541 c8541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5471
  · exact u5472
  · exact u5473
  · exact u5474

def b8542 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 70 28 73 178 162 226 162 418), lower := (rows 305 70 28 73 16 32 64 128 256), losses := [] }

theorem u8542 : Upper (D 1) (R 1) [304,68,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8542
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8543 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 28 74 179 163 227 163 419), lower := (rows 305 70 28 74 16 32 64 128 256), losses := [] }

theorem u8543 : Upper (D 1) (R 1) [304,68,24,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8543
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8544 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 70 28 104 147 163 195 131 387), lower := (rows 305 70 28 104 16 32 64 128 256), losses := [] }

theorem u8544 : Upper (D 1) (R 1) [304,68,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8544
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8545 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 28 137 242 226 226 226 482), lower := (rows 305 70 28 137 16 32 64 128 256), losses := [] }

theorem u8545 : Upper (D 1) (R 1) [304,68,24,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8545
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8546 : Route 9 := (fun mask => (mask,id))

def c8546 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8546 : Upper (D 1) (R 1) [304,68,24,130] 13 := by
  apply FastRouting.sound _ _ [304,68,24,130] 13 (by decide) (choices 1) [1,2,32,64,128] r8546 c8546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5475
  · exact u5476
  · exact u5477
  · exact u5478
  · exact u5479

def r8547 : Route 9 := (fun mask => (mask,id))

def c8547 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8547 : Upper (D 1) (R 1) [304,68,24,160] 13 := by
  apply FastRouting.sound _ _ [304,68,24,160] 13 (by decide) (choices 1) [1,2,64,128] r8547 c8547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5480
  · exact u5481
  · exact u5482
  · exact u5483

def b8548 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 70 28 200 179 163 227 163 419), lower := (rows 305 70 28 200 16 32 64 128 256), losses := [] }

theorem u8548 : Upper (D 1) (R 1) [304,68,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8548
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8549 : Route 9 := (fun mask => (mask,id))

def c8549 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u8549 : Upper (D 1) (R 1) [304,68,129,18] 13 := by
  apply FastRouting.sound _ _ [304,68,129,18] 13 (by decide) (choices 1) [2,8,32,64,128] r8549 c8549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5484
  · exact u5485
  · exact u5486
  · exact u5487
  · exact u5488

def b8550 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 70 133 56 218 234 202 202 458), lower := (rows 305 70 133 56 16 32 64 128 256), losses := [] }

theorem u8550 : Upper (D 1) (R 1) [304,68,129,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8550
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8551 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 133 74 186 186 250 186 442), lower := (rows 305 70 133 74 16 32 64 128 256), losses := [] }

theorem u8551 : Upper (D 1) (R 1) [304,68,129,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8551
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8552 : Route 9 := (fun mask => (mask,id))

def c8552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8552 : Upper (D 1) (R 1) [304,68,129,80] 13 := by
  apply FastRouting.sound _ _ [304,68,129,80] 13 (by decide) (choices 1) [2,8,32,128] r8552 c8552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5489
  · exact u5490
  · exact u5491
  · exact u5492

def b8553 : PairBound 9 := { available := 122, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 133 138 122 122 122 250 378), lower := (rows 305 70 133 138 16 32 64 128 256), losses := [] }

theorem u8553 : Upper (D 1) (R 1) [304,68,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8553
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8554 : Route 9 := (fun mask => (mask,id))

def c8554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8554 : Upper (D 1) (R 1) [304,68,129,144] 13 := by
  apply FastRouting.sound _ _ [304,68,129,144] 13 (by decide) (choices 1) [2,8,32,64] r8554 c8554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5493
  · exact u5494
  · exact u5495
  · exact u5496

def r8555 : Route 9 := (fun mask => (mask,id))

def c8555 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8555 : Upper (D 1) (R 1) [304,68,129,192] 13 := by
  apply FastRouting.sound _ _ [304,68,129,192] 13 (by decide) (choices 1) [2,8,32] r8555 c8555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5497
  · exact u5498
  · exact u5499

def b8556 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 134 11 248 248 248 248 504), lower := (rows 305 70 134 11 16 32 64 128 256), losses := [] }

theorem u8556 : Upper (D 1) (R 1) [304,68,130,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8556
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8557 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 70 134 25 250 234 234 234 490), lower := (rows 305 70 134 25 16 32 64 128 256), losses := [] }

theorem u8557 : Upper (D 1) (R 1) [304,68,130,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8557
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8558 : PairBound 9 := { available := 233, camps := [{ cop := 3, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 134 26 249 233 233 233 489), lower := (rows 305 70 134 26 16 32 64 128 256), losses := [] }

theorem u8558 : Upper (D 1) (R 1) [304,68,130,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8558
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8559 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 70 134 56 219 235 203 203 459), lower := (rows 305 70 134 56 16 32 64 128 256), losses := [] }

theorem u8559 : Upper (D 1) (R 1) [304,68,130,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8559
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8560 : Route 9 := (fun mask => (mask,id))

def c8560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8560 : Upper (D 1) (R 1) [304,68,130,65] 13 := by
  apply FastRouting.sound _ _ [304,68,130,65] 13 (by decide) (choices 1) [2,8,32,128] r8560 c8560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5500
  · exact u5501
  · exact u5502
  · exact u5503

def b8561 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 134 74 185 185 249 185 441), lower := (rows 305 70 134 74 16 32 64 128 256), losses := [] }

theorem u8561 : Upper (D 1) (R 1) [304,68,130,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8561
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8562 : Route 9 := (fun mask => (mask,id))

def c8562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8562 : Upper (D 1) (R 1) [304,68,130,80] 13 := by
  apply FastRouting.sound _ _ [304,68,130,80] 13 (by decide) (choices 1) [1,2,8,32,128] r8562 c8562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5504
  · exact u5505
  · exact u5506
  · exact u5507
  · exact u5508

def r8563 : Route 9 := (fun mask => (mask,id))

def c8563 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8563 : Upper (D 1) (R 1) [304,68,130,129] 13 := by
  apply FastRouting.sound _ _ [304,68,130,129] 13 (by decide) (choices 1) [2,8,32,64] r8563 c8563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5509
  · exact u5510
  · exact u5511
  · exact u5512

def b8564 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 134 138 121 121 121 249 377), lower := (rows 305 70 134 138 16 32 64 128 256), losses := [] }

theorem u8564 : Upper (D 1) (R 1) [304,68,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8564
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8565 : Route 9 := (fun mask => (mask,id))

def c8565 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8565 : Upper (D 1) (R 1) [304,68,130,144] 13 := by
  apply FastRouting.sound _ _ [304,68,130,144] 13 (by decide) (choices 1) [1,2,8,32,64] r8565 c8565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5513
  · exact u5514
  · exact u5515
  · exact u5516
  · exact u5517

def b8566 : PairBound 9 := { available := 59, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 134 200 59 59 123 187 315), lower := (rows 305 70 134 200 16 32 64 128 256), losses := [] }

theorem u8566 : Upper (D 1) (R 1) [304,68,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8566
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8567 : Route 9 := (fun mask => (mask,id))

def c8567 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8567 : Upper (D 1) (R 1) [304,68,136,3] 13 := by
  apply FastRouting.sound _ _ [304,68,136,3] 13 (by decide) (choices 1) [2,32,64,128] r8567 c8567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5518
  · exact u5519
  · exact u5520
  · exact u5521

def b8568 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 70 140 25 242 226 226 226 482), lower := (rows 305 70 140 25 16 32 64 128 256), losses := [] }

theorem u8568 : Upper (D 1) (R 1) [304,68,136,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8568
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8569 : Route 9 := (fun mask => (mask,id))

def c8569 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8569 : Upper (D 1) (R 1) [304,68,136,18] 13 := by
  apply FastRouting.sound _ _ [304,68,136,18] 13 (by decide) (choices 1) [1,2,32,64,128] r8569 c8569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5522
  · exact u5523
  · exact u5524
  · exact u5525
  · exact u5526

def b8570 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 70 140 56 211 227 195 195 451), lower := (rows 305 70 140 56 16 32 64 128 256), losses := [] }

theorem u8570 : Upper (D 1) (R 1) [304,68,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8570
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8571 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 70 140 73 178 178 242 178 434), lower := (rows 305 70 140 73 16 32 64 128 256), losses := [] }

theorem u8571 : Upper (D 1) (R 1) [304,68,136,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8571
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8572 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 140 74 179 179 243 179 435), lower := (rows 305 70 140 74 16 32 64 128 256), losses := [] }

theorem u8572 : Upper (D 1) (R 1) [304,68,136,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8572
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8573 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 70 140 88 179 163 227 163 419), lower := (rows 305 70 140 88 16 32 64 128 256), losses := [] }

theorem u8573 : Upper (D 1) (R 1) [304,68,136,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8573
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8574 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 140 137 114 114 114 242 370), lower := (rows 305 70 140 137 16 32 64 128 256), losses := [] }

theorem u8574 : Upper (D 1) (R 1) [304,68,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8574
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8575 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 140 138 115 115 115 243 371), lower := (rows 305 70 140 138 16 32 64 128 256), losses := [] }

theorem u8575 : Upper (D 1) (R 1) [304,68,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8575
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8576 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 140 152 115 99 99 227 355), lower := (rows 305 70 140 152 16 32 64 128 256), losses := [] }

theorem u8576 : Upper (D 1) (R 1) [304,68,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8576
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8577 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 140 200 51 51 115 179 307), lower := (rows 305 70 140 200 16 32 64 128 256), losses := [] }

theorem u8577 : Upper (D 1) (R 1) [304,68,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8577
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8578 : Route 9 := (fun mask => (mask,id))

def c8578 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u8578 : Upper (D 1) (R 1) [304,68,144,3] 13 := by
  apply FastRouting.sound _ _ [304,68,144,3] 13 (by decide) (choices 1) [2,8,32,64,128] r8578 c8578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5527
  · exact u5528
  · exact u5529
  · exact u5530
  · exact u5531

def b8579 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 70 148 41 218 234 202 202 458), lower := (rows 305 70 148 41 16 32 64 128 256), losses := [] }

theorem u8579 : Upper (D 1) (R 1) [304,68,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8579
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u8579
end Delivery.IrregularNine14.P01
