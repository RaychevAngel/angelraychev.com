import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0017
import IrregularNine14P05C0018

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3540 : Route 9 := (fun mask => (mask,id))

def c3540 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3540 : Upper (D 5) (R 5) [18,33,65,160,264,4] 13 := by
  apply FastRouting.sound _ _ [18,33,65,160,264,4] 13 (by decide) (choices 1) [2,4,8] r3540 c3540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1064
  · exact u1065
  · exact u1066

def b3541 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 35 69 168 280 40 70 134 262), lower := (rows 19 35 69 168 280 40 64 128 256), losses := [] }

theorem u3541 : Upper (D 5) (R 5) [18,33,65,160,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3541
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3542 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 392 28 34 108 172 300), lower := (rows 19 35 69 392 28 34 64 128 256), losses := [] }

theorem u3542 : Upper (D 5) (R 5) [18,33,65,384,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3542
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3543 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 392, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 35 69 392 28 36 106 170 298), lower := (rows 19 35 69 392 28 36 64 128 256), losses := [] }

theorem u3543 : Upper (D 5) (R 5) [18,33,65,384,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3543
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3544 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 35, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 69 392 28 40 102 166 294), lower := (rows 19 35 69 392 28 40 64 128 256), losses := [] }

theorem u3544 : Upper (D 5) (R 5) [18,33,65,384,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3544
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3545 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 140 276 33 104 168 296), lower := (rows 19 35 70 140 276 33 64 128 256), losses := [] }

theorem u3545 : Upper (D 5) (R 5) [18,33,66,132,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3545
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3546 : Route 9 := (fun mask => (mask,id))

def c3546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3546 : Upper (D 5) (R 5) [18,33,66,132,260,8] 13 := by
  apply FastRouting.sound _ _ [18,33,66,132,260,8] 13 (by decide) (choices 1) [1,8,32] r3546 c3546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1067
  · exact u1068
  · exact u1069

def b3547 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 140 280 33 108 172 300), lower := (rows 19 35 70 140 280 33 64 128 256), losses := [] }

theorem u3547 : Upper (D 5) (R 5) [18,33,66,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3547
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3548 : PairBound 9 := { available := 41, camps := [], pairs := [(0,3),(1,3)], upper := (rows 19 35 70 140 280 36 105 169 297), lower := (rows 19 35 70 140 280 36 64 128 256), losses := [{ target := 3, region := (rows 17 18 4 0 16 44 64 128 256), good := (rows 19 35 102 164 307 36 64 128 256) }] }

theorem u3548 : Upper (D 5) (R 5) [18,33,66,132,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3548
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3549 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 35, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 70 140 280 40 101 165 293), lower := (rows 19 35 70 140 280 40 64 128 256), losses := [] }

theorem u3549 : Upper (D 5) (R 5) [18,33,66,132,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3549
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3550 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 168 28 33 332 396 268), lower := (rows 19 35 70 168 28 33 64 128 256), losses := [] }

theorem u3550 : Upper (D 5) (R 5) [18,33,66,160,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3550
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3551 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 70 168 28 36 329 393 265), lower := (rows 19 35 70 168 28 36 64 128 256), losses := [] }

theorem u3551 : Upper (D 5) (R 5) [18,33,66,160,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3551
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3552 : PairBound 9 := { available := 261, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 35 70 168 28 40 325 389 261), lower := (rows 19 35 70 168 28 40 64 128 256), losses := [] }

theorem u3552 : Upper (D 5) (R 5) [18,33,66,160,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3552
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3553 : Route 9 := (fun mask => (mask,id))

def c3553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3553 : Upper (D 5) (R 5) [18,33,66,160,12,256] 13 := by
  apply FastRouting.sound _ _ [18,33,66,160,12,256] 13 (by decide) (choices 1) [1,4,8] r3553 c3553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1070
  · exact u1071
  · exact u1072

def b3554 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 168 276 33 76 140 268), lower := (rows 19 35 70 168 276 33 64 128 256), losses := [] }

theorem u3554 : Upper (D 5) (R 5) [18,33,66,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3554
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3555 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 70 168 276 36 73 137 265), lower := (rows 19 35 70 168 276 36 64 128 256), losses := [] }

theorem u3555 : Upper (D 5) (R 5) [18,33,66,160,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3555
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3556 : PairBound 9 := { available := 13, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 35 70 168 276 40 77 141 269), lower := (rows 19 35 70 168 276 40 64 128 256), losses := [] }

theorem u3556 : Upper (D 5) (R 5) [18,33,66,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3556
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3557 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 168 280 33 76 140 268), lower := (rows 19 35 70 168 280 33 64 128 256), losses := [] }

theorem u3557 : Upper (D 5) (R 5) [18,33,66,160,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3557
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3558 : Route 9 := (fun mask => (mask,id))

def c3558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3558 : Upper (D 5) (R 5) [18,33,66,160,264,4] 13 := by
  apply FastRouting.sound _ _ [18,33,66,160,264,4] 13 (by decide) (choices 1) [1,4,8] r3558 c3558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1073
  · exact u1074
  · exact u1075

def b3559 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 35 70 168 280 40 69 133 261), lower := (rows 19 35 70 168 280 40 64 128 256), losses := [] }

theorem u3559 : Upper (D 5) (R 5) [18,33,66,160,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3559
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3560 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 392 28 33 108 172 300), lower := (rows 19 35 70 392 28 33 64 128 256), losses := [] }

theorem u3560 : Upper (D 5) (R 5) [18,33,66,384,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3560
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3561 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 70 392 28 36 105 169 297), lower := (rows 19 35 70 392 28 36 64 128 256), losses := [] }

theorem u3561 : Upper (D 5) (R 5) [18,33,66,384,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3561
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3562 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 35, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 70 392 28 40 101 165 293), lower := (rows 19 35 70 392 28 40 64 128 256), losses := [] }

theorem u3562 : Upper (D 5) (R 5) [18,33,66,384,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3562
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3563 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 140 276 33 106 170 298), lower := (rows 19 35 76 140 276 33 64 128 256), losses := [] }

theorem u3563 : Upper (D 5) (R 5) [18,33,72,132,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3563
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3564 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 140 276 34 105 169 297), lower := (rows 19 35 76 140 276 34 64 128 256), losses := [] }

theorem u3564 : Upper (D 5) (R 5) [18,33,72,132,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3564
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3565 : PairBound 9 := { available := 35, camps := [], pairs := [(0,2),(1,2)], upper := (rows 19 35 76 140 276 40 99 163 291), lower := (rows 19 35 76 140 276 40 64 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 44 82 146 274), good := (rows 467 483 104 168 499 40 64 128 256) }] }

theorem u3565 : Upper (D 5) (R 5) [18,33,72,132,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3565
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3566 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 168 276 33 78 142 270), lower := (rows 19 35 76 168 276 33 64 128 256), losses := [] }

theorem u3566 : Upper (D 5) (R 5) [18,33,72,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3566
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3567 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 168 276 34 77 141 269), lower := (rows 19 35 76 168 276 34 64 128 256), losses := [] }

theorem u3567 : Upper (D 5) (R 5) [18,33,72,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3567
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3568 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 76 168 276 36 75 139 267), lower := (rows 19 35 76 168 276 36 64 128 256), losses := [] }

theorem u3568 : Upper (D 5) (R 5) [18,33,72,160,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3568
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3569 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 35 76 168 276 40 71 135 263), lower := (rows 19 35 76 168 276 40 64 128 256), losses := [] }

theorem u3569 : Upper (D 5) (R 5) [18,33,72,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3569
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3570 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 168 280 33 70 134 262), lower := (rows 19 35 76 168 280 33 64 128 256), losses := [] }

theorem u3570 : Upper (D 5) (R 5) [18,33,72,160,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3570
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3571 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 168 280 34 69 133 261), lower := (rows 19 35 76 168 280 34 64 128 256), losses := [] }

theorem u3571 : Upper (D 5) (R 5) [18,33,72,160,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3571
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3572 : Route 9 := (fun mask => (mask,id))

def c3572 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3572 : Upper (D 5) (R 5) [18,33,72,160,264,4] 13 := by
  apply FastRouting.sound _ _ [18,33,72,160,264,4] 13 (by decide) (choices 1) [1,2,4] r3572 c3572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1076
  · exact u1077
  · exact u1078

def b3573 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 100 392 28 33 78 142 270), lower := (rows 19 35 100 392 28 33 64 128 256), losses := [] }

theorem u3573 : Upper (D 5) (R 5) [18,33,96,384,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3573
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3574 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 100 392 28 34 77 141 269), lower := (rows 19 35 100 392 28 34 64 128 256), losses := [] }

theorem u3574 : Upper (D 5) (R 5) [18,33,96,384,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3574
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3575 : PairBound 9 := { available := 11, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 100 392 28 36 75 139 267), lower := (rows 19 35 100 392 28 36 64 128 256), losses := [] }

theorem u3575 : Upper (D 5) (R 5) [18,33,96,384,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3575
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3576 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 35, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 100 392 28 40 71 135 263), lower := (rows 19 35 100 392 28 40 64 128 256), losses := [] }

theorem u3576 : Upper (D 5) (R 5) [18,33,96,384,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3576
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3577 : PairBound 9 := { available := 264, camps := [{ cop := 3, region := 324, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 38 69 41 148 34 328 392 264), lower := (rows 19 38 69 41 148 34 64 128 256), losses := [] }

theorem u3577 : Upper (D 5) (R 5) [18,36,65,33,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3577
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3578 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 40, targets := 2 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 69 41 148 40 330 394 266), lower := (rows 19 38 69 41 148 40 64 128 256), losses := [] }

theorem u3578 : Upper (D 5) (R 5) [18,36,65,33,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3578
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3579 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 19 38 69 41 148 288 74 138 266), lower := (rows 19 38 69 41 148 288 64 128 256), losses := [] }

theorem u3579 : Upper (D 5) (R 5) [18,36,65,33,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3579
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3580 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 324, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 38 69 41 152 34 332 396 268), lower := (rows 19 38 69 41 152 34 64 128 256), losses := [] }

theorem u3580 : Upper (D 5) (R 5) [18,36,65,33,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3580
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3581 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 69 41 152 36 330 394 266), lower := (rows 19 38 69 41 152 36 64 128 256), losses := [] }

theorem u3581 : Upper (D 5) (R 5) [18,36,65,33,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3581
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3582 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 69 41 152 40 326 390 262), lower := (rows 19 38 69 41 152 40 64 128 256), losses := [] }

theorem u3582 : Upper (D 5) (R 5) [18,36,65,33,136,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3582
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3583 : Route 9 := (fun mask => (mask,id))

def c3583 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3583 : Upper (D 5) (R 5) [18,36,65,33,136,256] 13 := by
  apply FastRouting.sound _ _ [18,36,65,33,136,256] 13 (by decide) (choices 1) [2,4,8] r3583 c3583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1079
  · exact u1080
  · exact u1081

def b3584 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 38 69 41 400 34 76 140 268), lower := (rows 19 38 69 41 400 34 64 128 256), losses := [] }

theorem u3584 : Upper (D 5) (R 5) [18,36,65,33,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3584
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3585 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 69 41 400 36 74 138 266), lower := (rows 19 38 69 41 400 36 64 128 256), losses := [] }

theorem u3585 : Upper (D 5) (R 5) [18,36,65,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3585
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3586 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 69 41 400 40 78 142 270), lower := (rows 19 38 69 41 400 40 64 128 256), losses := [] }

theorem u3586 : Upper (D 5) (R 5) [18,36,65,33,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3586
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3587 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 69 137 276 34 104 168 296), lower := (rows 19 38 69 137 276 34 64 128 256), losses := [] }

theorem u3587 : Upper (D 5) (R 5) [18,36,65,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3587
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3588 : Route 9 := (fun mask => (mask,id))

def c3588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3588 : Upper (D 5) (R 5) [18,36,65,129,260,8] 13 := by
  apply FastRouting.sound _ _ [18,36,65,129,260,8] 13 (by decide) (choices 1) [2,8,32] r3588 c3588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1082
  · exact u1083
  · exact u1084

def b3589 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 69 137 280 34 108 172 300), lower := (rows 19 38 69 137 280 34 64 128 256), losses := [] }

theorem u3589 : Upper (D 5) (R 5) [18,36,65,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3589
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3590 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 69 137 280 36 106 170 298), lower := (rows 19 38 69 137 280 36 64 128 256), losses := [] }

theorem u3590 : Upper (D 5) (R 5) [18,36,65,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3590
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3591 : Route 9 := (fun mask => (mask,id))

def c3591 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3591 : Upper (D 5) (R 5) [18,36,65,129,264,8] 13 := by
  apply FastRouting.sound _ _ [18,36,65,129,264,8] 13 (by decide) (choices 1) [2,4,32] r3591 c3591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1085
  · exact u1086
  · exact u1087

def b3592 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 38 69 138 28 33 360 424 296), lower := (rows 19 38 69 138 28 33 64 128 256), losses := [] }

theorem u3592 : Upper (D 5) (R 5) [18,36,65,130,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3592
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3593 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 424, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(3,2)], upper := (rows 19 38 69 138 28 40 353 417 289), lower := (rows 19 38 69 138 28 40 64 128 256), losses := [] }

theorem u3593 : Upper (D 5) (R 5) [18,36,65,130,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3593
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3594 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 424, targets := 4 }], pairs := [(3,2)], upper := (rows 19 38 69 138 28 288 105 169 297), lower := (rows 19 38 69 138 28 288 64 128 256), losses := [] }

theorem u3594 : Upper (D 5) (R 5) [18,36,65,130,12,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3594
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3595 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 38 69 138 276 33 104 168 296), lower := (rows 19 38 69 138 276 33 64 128 256), losses := [] }

theorem u3595 : Upper (D 5) (R 5) [18,36,65,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3595
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3596 : Route 9 := (fun mask => (mask,id))

def c3596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3596 : Upper (D 5) (R 5) [18,36,65,130,260,8] 13 := by
  apply FastRouting.sound _ _ [18,36,65,130,260,8] 13 (by decide) (choices 1) [1,8,32] r3596 c3596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1088
  · exact u1089
  · exact u1090

def b3597 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 38 69 138 280 33 108 172 300), lower := (rows 19 38 69 138 280 33 64 128 256), losses := [] }

theorem u3597 : Upper (D 5) (R 5) [18,36,65,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3597
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3598 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 69 138 280 36 105 169 297), lower := (rows 19 38 69 138 280 36 64 128 256), losses := [] }

theorem u3598 : Upper (D 5) (R 5) [18,36,65,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3598
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3599 : Route 9 := (fun mask => (mask,id))

def c3599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3599 : Upper (D 5) (R 5) [18,36,65,130,264,8] 13 := by
  apply FastRouting.sound _ _ [18,36,65,130,264,8] 13 (by decide) (choices 1) [1,4,32] r3599 c3599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1091
  · exact u1092
  · exact u1093

#print axioms u3599
end Delivery.IrregularNine14.P05
