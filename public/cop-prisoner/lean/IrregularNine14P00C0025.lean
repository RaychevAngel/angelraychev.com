import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0007

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1500 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 51 259 84 200 24 165 229 165 421), lower := (rows 51 259 84 200 24 32 64 128 256), losses := [] }

theorem u1500 : Upper (D 0) (R 0) [50,257,80,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1500
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1501 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 259 84 200 48 173 205 141 397), lower := (rows 51 259 84 200 48 32 64 128 256), losses := [] }

theorem u1501 : Upper (D 0) (R 0) [50,257,80,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1501
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1502 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 84 200 144 45 109 173 301), lower := (rows 51 259 84 200 144 32 64 128 256), losses := [] }

theorem u1502 : Upper (D 0) (R 0) [50,257,80,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1502
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1503 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 51 262 13 200 17 240 240 240 496), lower := (rows 51 262 13 200 17 32 64 128 256), losses := [] }

theorem u1503 : Upper (D 0) (R 0) [50,260,9,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1503
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1504 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 13 200 48 241 209 209 465), lower := (rows 51 262 13 200 48 32 64 128 256), losses := [] }

theorem u1504 : Upper (D 0) (R 0) [50,260,9,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1504
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1505 : PairBound 9 := { available := 177, camps := [], pairs := [(1,6)], upper := (rows 51 262 13 200 80 177 241 177 433), lower := (rows 51 262 13 200 80 32 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 33 0 129 257), good := (rows 435 262 431 136 16 32 0 128 256) }] }

theorem u1505 : Upper (D 0) (R 0) [50,260,9,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1505
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1506 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 262 69 88 17 168 232 168 424), lower := (rows 51 262 69 88 17 32 64 128 256), losses := [] }

theorem u1506 : Upper (D 0) (R 0) [50,260,65,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1506
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1507 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 262 69 88 24 161 225 161 417), lower := (rows 51 262 69 88 24 32 64 128 256), losses := [] }

theorem u1507 : Upper (D 0) (R 0) [50,260,65,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1507
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1508 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 88 48 169 201 137 393), lower := (rows 51 262 69 88 48 32 64 128 256), losses := [] }

theorem u1508 : Upper (D 0) (R 0) [50,260,65,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1508
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1509 : Route 9 := (fun mask => (mask,id))

def c1509 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1509 : Upper (D 0) (R 0) [50,260,65,80,128] 13 := by
  apply FastRouting.sound _ _ [50,260,65,80,128] 13 (by decide) (choices 1) [1,8,128] r1509 c1509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u446
  · exact u447
  · exact u448

def b1510 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 262 69 137 24 240 240 240 496), lower := (rows 51 262 69 137 24 32 64 128 256), losses := [] }

theorem u1510 : Upper (D 0) (R 0) [50,260,65,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1510
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1511 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 137 48 248 216 216 472), lower := (rows 51 262 69 137 48 32 64 128 256), losses := [] }

theorem u1511 : Upper (D 0) (R 0) [50,260,65,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1511
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1512 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 69 137 80 184 248 184 440), lower := (rows 51 262 69 137 80 32 64 128 256), losses := [] }

theorem u1512 : Upper (D 0) (R 0) [50,260,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1512
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1513_8 : Upper (D 0) (R 0) [50,260,65,129,128,8] 13 :=
  permutation_upper _ _ _ [50,260,65,129,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u449

theorem m1513_16 : Upper (D 0) (R 0) [50,260,65,129,128,16] 13 :=
  permutation_upper _ _ _ [50,260,65,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u450

theorem m1513_64 : Upper (D 0) (R 0) [50,260,65,129,128,64] 13 :=
  permutation_upper _ _ _ [50,260,65,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u451

def r1513 : Route 9 := (fun mask => (mask,id))

def c1513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1513 : Upper (D 0) (R 0) [50,260,65,129,128] 13 := by
  apply FastRouting.sound _ _ [50,260,65,129,128] 13 (by decide) (choices 1) [8,16,64] r1513 c1513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1513_8
  · exact m1513_16
  · exact m1513_64

def b1514 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 51 262 69 152 17 232 232 232 488), lower := (rows 51 262 69 152 17 32 64 128 256), losses := [] }

theorem u1514 : Upper (D 0) (R 0) [50,260,65,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1514
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1515 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 262 69 152 24 225 225 225 481), lower := (rows 51 262 69 152 24 32 64 128 256), losses := [] }

theorem u1515 : Upper (D 0) (R 0) [50,260,65,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1515
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1516 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 152 48 233 201 201 457), lower := (rows 51 262 69 152 48 32 64 128 256), losses := [] }

theorem u1516 : Upper (D 0) (R 0) [50,260,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1516
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1517 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 69 152 80 169 233 169 425), lower := (rows 51 262 69 152 80 32 64 128 256), losses := [] }

theorem u1517 : Upper (D 0) (R 0) [50,260,65,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1517
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1518 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 262 69 152 144 105 105 233 361), lower := (rows 51 262 69 152 144 32 64 128 256), losses := [] }

theorem u1518 : Upper (D 0) (R 0) [50,260,65,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1518
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1519 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 51 262 69 200 17 184 248 184 440), lower := (rows 51 262 69 200 17 32 64 128 256), losses := [] }

theorem u1519 : Upper (D 0) (R 0) [50,260,65,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1519
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1520 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 262 69 200 24 177 241 177 433), lower := (rows 51 262 69 200 24 32 64 128 256), losses := [] }

theorem u1520 : Upper (D 0) (R 0) [50,260,65,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1520
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1521 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 200 48 185 217 153 409), lower := (rows 51 262 69 200 48 32 64 128 256), losses := [] }

theorem u1521 : Upper (D 0) (R 0) [50,260,65,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1521
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1522_1 : Upper (D 0) (R 0) [50,260,65,192,128,1] 13 :=
  permutation_upper _ _ _ [50,260,65,192,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u452

theorem m1522_8 : Upper (D 0) (R 0) [50,260,65,192,128,8] 13 :=
  permutation_upper _ _ _ [50,260,65,192,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u453

theorem m1522_16 : Upper (D 0) (R 0) [50,260,65,192,128,16] 13 :=
  permutation_upper _ _ _ [50,260,65,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u454

def r1522 : Route 9 := (fun mask => (mask,id))

def c1522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1522 : Upper (D 0) (R 0) [50,260,65,192,128] 13 := by
  apply FastRouting.sound _ _ [50,260,65,192,128] 13 (by decide) (choices 1) [1,8,16] r1522 c1522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1522_1
  · exact m1522_8
  · exact m1522_16

def b1523 : PairBound 9 := { available := 240, camps := [], pairs := [(1,0)], upper := (rows 51 262 76 137 17 240 240 240 496), lower := (rows 51 262 76 137 17 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 49 81 145 273), good := (rows 498 262 78 494 496 32 64 128 256) }] }

theorem u1523 : Upper (D 0) (R 0) [50,260,72,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1523
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1524 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 76 137 48 241 209 209 465), lower := (rows 51 262 76 137 48 32 64 128 256), losses := [] }

theorem u1524 : Upper (D 0) (R 0) [50,260,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1524
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1525 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 76 137 80 177 241 177 433), lower := (rows 51 262 76 137 80 32 64 128 256), losses := [] }

theorem u1525 : Upper (D 0) (R 0) [50,260,72,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1525
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1526 : PairBound 9 := { available := 113, camps := [], pairs := [(1,7)], upper := (rows 51 262 76 137 144 113 113 241 369), lower := (rows 51 262 76 137 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 33 65 0 257), good := (rows 371 262 78 367 16 32 64 0 256) }] }

theorem u1526 : Upper (D 0) (R 0) [50,260,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1526
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1527 : PairBound 9 := { available := 225, camps := [], pairs := [(1,4)], upper := (rows 51 262 76 152 17 225 225 225 481), lower := (rows 51 262 76 152 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 10 12 8 0 49 81 145 273), good := (rows 483 262 78 494 481 32 64 128 256) }] }

theorem u1527 : Upper (D 0) (R 0) [50,260,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1527
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1528 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 76 152 48 225 193 193 449), lower := (rows 51 262 76 152 48 32 64 128 256), losses := [] }

theorem u1528 : Upper (D 0) (R 0) [50,260,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1528
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1529 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 76 152 80 161 225 161 417), lower := (rows 51 262 76 152 80 32 64 128 256), losses := [] }

theorem u1529 : Upper (D 0) (R 0) [50,260,72,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1529
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1530 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 262 76 152 144 97 97 225 353), lower := (rows 51 262 76 152 144 32 64 128 256), losses := [] }

theorem u1530 : Upper (D 0) (R 0) [50,260,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1530
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1531 : Route 9 := (fun mask => (mask,id))

def c1531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1531 : Upper (D 0) (R 0) [50,260,192,65,1] 13 := by
  apply FastRouting.sound _ _ [50,260,192,65,1] 13 (by decide) (choices 1) [8,16,128] r1531 c1531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u455
  · exact u456
  · exact u457

def b1532 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 262 196 73 24 177 241 177 433), lower := (rows 51 262 196 73 24 32 64 128 256), losses := [] }

theorem u1532 : Upper (D 0) (R 0) [50,260,192,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1532
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1533 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 196 73 48 185 217 153 409), lower := (rows 51 262 196 73 48 32 64 128 256), losses := [] }

theorem u1533 : Upper (D 0) (R 0) [50,260,192,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1533
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1534 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 51 262 196 73 144 57 121 185 313), lower := (rows 51 262 196 73 144 32 64 128 256), losses := [] }

theorem u1534 : Upper (D 0) (R 0) [50,260,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1534
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1535 : Route 9 := (fun mask => (mask,id))

def c1535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1535 : Upper (D 0) (R 0) [50,260,192,80,1] 13 := by
  apply FastRouting.sound _ _ [50,260,192,80,1] 13 (by decide) (choices 1) [1,8,128] r1535 c1535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u458
  · exact u459
  · exact u460

def b1536 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 262 196 88 24 161 225 161 417), lower := (rows 51 262 196 88 24 32 64 128 256), losses := [] }

theorem u1536 : Upper (D 0) (R 0) [50,260,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1536
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1537 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 196 88 48 169 201 137 393), lower := (rows 51 262 196 88 48 32 64 128 256), losses := [] }

theorem u1537 : Upper (D 0) (R 0) [50,260,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1537
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1538 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 51 262 196 88 144 41 105 169 297), lower := (rows 51 262 196 88 144 32 64 128 256), losses := [] }

theorem u1538 : Upper (D 0) (R 0) [50,260,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1538
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1539 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 13 140 17 240 240 240 496), lower := (rows 51 322 13 140 17 32 64 128 256), losses := [] }

theorem u1539 : Upper (D 0) (R 0) [50,320,9,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1539
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1540 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 13 140 48 241 209 209 465), lower := (rows 51 322 13 140 48 32 64 128 256), losses := [] }

theorem u1540 : Upper (D 0) (R 0) [50,320,9,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1540
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1541 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 13 140 80 177 241 177 433), lower := (rows 51 322 13 140 80 32 64 128 256), losses := [] }

theorem u1541 : Upper (D 0) (R 0) [50,320,9,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1541
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1542 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 51 322 13 140 144 113 113 241 369), lower := (rows 51 322 13 140 144 32 64 128 256), losses := [] }

theorem u1542 : Upper (D 0) (R 0) [50,320,9,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1542
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1543 : Route 9 := (fun mask => (mask,id))

def c1543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1543 : Upper (D 0) (R 0) [50,320,9,192,1] 13 := by
  apply FastRouting.sound _ _ [50,320,9,192,1] 13 (by decide) (choices 1) [4,16,128] r1543 c1543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u461
  · exact u462
  · exact u463

def b1544 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 322 13 200 20 177 241 177 433), lower := (rows 51 322 13 200 20 32 64 128 256), losses := [] }

theorem u1544 : Upper (D 0) (R 0) [50,320,9,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1544
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1545 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 13 200 48 181 213 149 405), lower := (rows 51 322 13 200 48 32 64 128 256), losses := [] }

theorem u1545 : Upper (D 0) (R 0) [50,320,9,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1545
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1546_1 : Upper (D 0) (R 0) [50,320,9,192,128,1] 13 :=
  permutation_upper _ _ _ [50,320,9,192,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u463

theorem m1546_4 : Upper (D 0) (R 0) [50,320,9,192,128,4] 13 :=
  permutation_upper _ _ _ [50,320,9,192,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u464

theorem m1546_16 : Upper (D 0) (R 0) [50,320,9,192,128,16] 13 :=
  permutation_upper _ _ _ [50,320,9,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u465

def r1546 : Route 9 := (fun mask => (mask,id))

def c1546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1546 : Upper (D 0) (R 0) [50,320,9,192,128] 13 := by
  apply FastRouting.sound _ _ [50,320,9,192,128] 13 (by decide) (choices 1) [1,4,16] r1546 c1546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1546_1
  · exact m1546_4
  · exact m1546_16

def r1547 : Route 9 := (fun mask => (mask,id))

def c1547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1547 : Upper (D 0) (R 0) [50,320,24,96,1] 13 := by
  apply FastRouting.sound _ _ [50,320,24,96,1] 13 (by decide) (choices 1) [1,4,128] r1547 c1547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u466
  · exact u467
  · exact u468

def b1548 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 51 322 28 104 20 161 193 129 385), lower := (rows 51 322 28 104 20 32 64 128 256), losses := [] }

theorem u1548 : Upper (D 0) (R 0) [50,320,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1548
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1549 : Route 9 := (fun mask => (mask,id))

def c1549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1549 : Upper (D 0) (R 0) [50,320,24,96,128] 13 := by
  apply FastRouting.sound _ _ [50,320,24,96,128] 13 (by decide) (choices 1) [1,4,128] r1549 c1549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u469
  · exact u470
  · exact u471

def b1550 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 28 137 17 228 228 228 484), lower := (rows 51 322 28 137 17 32 64 128 256), losses := [] }

theorem u1550 : Upper (D 0) (R 0) [50,320,24,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1550
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1551 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 322 28 137 20 225 225 225 481), lower := (rows 51 322 28 137 20 32 64 128 256), losses := [] }

theorem u1551 : Upper (D 0) (R 0) [50,320,24,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1551
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1552 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 28 137 48 229 197 197 453), lower := (rows 51 322 28 137 48 32 64 128 256), losses := [] }

theorem u1552 : Upper (D 0) (R 0) [50,320,24,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1552
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1553 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 28 137 80 165 229 165 421), lower := (rows 51 322 28 137 80 32 64 128 256), losses := [] }

theorem u1553 : Upper (D 0) (R 0) [50,320,24,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1553
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1554 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 28 137 144 101 101 229 357), lower := (rows 51 322 28 137 144 32 64 128 256), losses := [] }

theorem u1554 : Upper (D 0) (R 0) [50,320,24,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1554
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1555 : Route 9 := (fun mask => (mask,id))

def c1555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1555 : Upper (D 0) (R 0) [50,320,24,160,1] 13 := by
  apply FastRouting.sound _ _ [50,320,24,160,1] 13 (by decide) (choices 1) [1,4,64,128] r1555 c1555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u472
  · exact u473
  · exact u474
  · exact u475

def b1556 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 51 322 28 168 20 225 193 193 449), lower := (rows 51 322 28 168 20 32 64 128 256), losses := [] }

theorem u1556 : Upper (D 0) (R 0) [50,320,24,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1556
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1557 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 28 168 80 165 197 133 389), lower := (rows 51 322 28 168 80 32 64 128 256), losses := [] }

theorem u1557 : Upper (D 0) (R 0) [50,320,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1557
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1558 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 28 168 144 101 69 197 325), lower := (rows 51 322 28 168 144 32 64 128 256), losses := [] }

theorem u1558 : Upper (D 0) (R 0) [50,320,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1558
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1559 : Route 9 := (fun mask => (mask,id))

def c1559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1559 : Upper (D 0) (R 0) [50,320,24,192,1] 13 := by
  apply FastRouting.sound _ _ [50,320,24,192,1] 13 (by decide) (choices 1) [1,4,128] r1559 c1559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u476
  · exact u477
  · exact u478

#print axioms u1559
end Delivery.IrregularNine14.P00
