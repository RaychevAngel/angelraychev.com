import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0001

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1500 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 98 140 296 25 36 65 134 262), lower := (rows 19 98 140 296 25 36 65 128 256), losses := [] }

theorem u1500 : Upper (D 5) (R 5) [18,96,136,288,9,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1500
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1501 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 98 140 296 25 36 66 133 261), lower := (rows 19 98 140 296 25 36 66 128 256), losses := [] }

theorem u1501 : Upper (D 5) (R 5) [18,96,136,288,9,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1501
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1502 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 98 140 296 25 36 68 131 259), lower := (rows 19 98 140 296 25 36 68 128 256), losses := [] }

theorem u1502 : Upper (D 5) (R 5) [18,96,136,288,9,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1502
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1503 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 194 38 268 25 40 65 164 292), lower := (rows 19 194 38 268 25 40 65 128 256), losses := [] }

theorem u1503 : Upper (D 5) (R 5) [18,192,34,260,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1503
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m1504_1 : Upper (D 5) (R 5) [18,192,34,260,9,8,4,1] 13 :=
  permutation_upper _ _ _ [18,192,34,260,9,8,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u84

def r1504 : Route 9 := (fun mask => (mask,id))

def c1504 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1504 : Upper (D 5) (R 5) [18,192,34,260,9,8,4] 13 := by
  apply FastRouting.sound _ _ [18,192,34,260,9,8,4] 13 (by decide) (choices 1) [1,32] r1504 c1504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m1504_1
  · exact u85

def b1505 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 194 38 268 25 40 96 133 261), lower := (rows 19 194 38 268 25 40 96 128 256), losses := [] }

theorem u1505 : Upper (D 5) (R 5) [18,192,34,260,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1505
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1506 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 194 38 268 56 33 65 140 268), lower := (rows 19 194 38 268 56 33 65 128 256), losses := [] }

theorem u1506 : Upper (D 5) (R 5) [18,192,34,260,40,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1506
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1507 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 36, targets := 8 }], pairs := [(0,5),(2,3)], upper := (rows 19 194 38 268 56 33 68 137 265), lower := (rows 19 194 38 268 56 33 68 128 256), losses := [{ target := 5, region := (rows 17 18 4 8 16 0 76 144 272), good := (rows 403 194 70 332 475 1 68 128 256) }] }

theorem u1507 : Upper (D 5) (R 5) [18,192,34,260,40,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1507
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m1508_1 : Upper (D 5) (R 5) [18,192,34,260,40,1,8,1] 13 :=
  permutation_upper _ _ _ [18,192,34,260,40,1,1,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u86

theorem m1508_4 : Upper (D 5) (R 5) [18,192,34,260,40,1,8,4] 13 :=
  permutation_upper _ _ _ [18,192,34,260,40,1,4,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u87

def r1508 : Route 9 := (fun mask => (mask,id))

def c1508 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1508 : Upper (D 5) (R 5) [18,192,34,260,40,1,8] 13 := by
  apply FastRouting.sound _ _ [18,192,34,260,40,1,8] 13 (by decide) (choices 1) [1,4] r1508 c1508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m1508_1
  · exact m1508_4

def b1509 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 268, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 194 44 268 21 34 65 168 296), lower := (rows 19 194 44 268 21 34 65 128 256), losses := [] }

theorem u1509 : Upper (D 5) (R 5) [18,192,40,260,5,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1509
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1510 : PairBound 9 := { available := 33, camps := [], pairs := [(0,2),(1,2)], upper := (rows 19 194 44 268 21 34 72 161 289), lower := (rows 19 194 44 268 21 34 72 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 51 76 145 273), good := (rows 435 226 104 328 499 34 72 128 256) }] }

theorem u1510 : Upper (D 5) (R 5) [18,192,40,260,5,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1510
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1511 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 98, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 194 44 268 21 34 96 137 265), lower := (rows 19 194 44 268 21 34 96 128 256), losses := [] }

theorem u1511 : Upper (D 5) (R 5) [18,192,40,260,5,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1511
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1512 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 268, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 194 44 268 25 34 65 164 292), lower := (rows 19 194 44 268 25 34 65 128 256), losses := [] }

theorem u1512 : Upper (D 5) (R 5) [18,192,40,260,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1512
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1513 : PairBound 9 := { available := 33, camps := [], pairs := [(0,3),(2,0)], upper := (rows 19 194 44 268 25 34 68 161 289), lower := (rows 19 194 44 268 25 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 35 93 128 256), good := (rows 118 226 108 332 124 34 68 128 256) },{ target := 3, region := (rows 17 18 4 0 16 51 76 145 273), good := (rows 435 226 100 324 499 34 68 128 256) }] }

theorem u1513 : Upper (D 5) (R 5) [18,192,40,260,9,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1513
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1514 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 98, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 194 44 268 25 34 96 133 261), lower := (rows 19 194 44 268 25 34 96 128 256), losses := [] }

theorem u1514 : Upper (D 5) (R 5) [18,192,40,260,9,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1514
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1515 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 67 44 137 22 288 68 152 280), lower := (rows 35 67 44 137 22 288 68 128 256), losses := [] }

theorem u1515 : Upper (D 5) (R 5) [34,65,40,129,6,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1515
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1516 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 67, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 44 137 22 288 72 148 276), lower := (rows 35 67 44 137 22 288 72 128 256), losses := [] }

theorem u1516 : Upper (D 5) (R 5) [34,65,40,129,6,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1516
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1517 : PairBound 9 := { available := 12, camps := [], pairs := [], upper := (rows 35 67 44 137 22 288 80 140 268), lower := (rows 35 67 44 137 22 288 80 128 256), losses := [] }

theorem u1517 : Upper (D 5) (R 5) [34,65,40,129,6,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1517
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1518 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 308, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 137 276 48 66 140 268), lower := (rows 35 67 44 137 276 48 66 128 256), losses := [] }

theorem u1518 : Upper (D 5) (R 5) [34,65,40,129,260,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1518
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1519 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 136, targets := 4 }], pairs := [(3,2)], upper := (rows 35 67 44 137 276 48 68 138 266), lower := (rows 35 67 44 137 276 48 68 128 256), losses := [] }

theorem u1519 : Upper (D 5) (R 5) [34,65,40,129,260,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1519
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1520 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 67, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 44 137 276 48 72 134 262), lower := (rows 35 67 44 137 276 48 72 128 256), losses := [] }

theorem u1520 : Upper (D 5) (R 5) [34,65,40,129,260,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1520
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1521 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 308, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 138 276 48 65 140 268), lower := (rows 35 67 44 138 276 48 65 128 256), losses := [] }

theorem u1521 : Upper (D 5) (R 5) [34,65,40,130,260,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1521
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1522 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 4 }], pairs := [(3,2)], upper := (rows 35 67 44 138 276 48 68 137 265), lower := (rows 35 67 44 138 276 48 68 128 256), losses := [] }

theorem u1522 : Upper (D 5) (R 5) [34,65,40,130,260,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1522
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1523 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 44 138 276 48 72 133 261), lower := (rows 35 67 44 138 276 48 72 128 256), losses := [] }

theorem u1523 : Upper (D 5) (R 5) [34,65,40,130,260,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1523
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1524 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 140 22 288 65 152 280), lower := (rows 35 67 44 140 22 288 65 128 256), losses := [] }

theorem u1524 : Upper (D 5) (R 5) [34,65,40,132,6,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1524
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1525 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 44 140 22 288 72 145 273), lower := (rows 35 67 44 140 22 288 72 128 256), losses := [] }

theorem u1525 : Upper (D 5) (R 5) [34,65,40,132,6,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1525
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1526 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 67 44 140 22 288 80 137 265), lower := (rows 35 67 44 140 22 288 80 128 256), losses := [] }

theorem u1526 : Upper (D 5) (R 5) [34,65,40,132,6,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1526
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1527 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 292, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 140 26 288 65 148 276), lower := (rows 35 67 44 140 26 288 65 128 256), losses := [] }

theorem u1527 : Upper (D 5) (R 5) [34,65,40,132,10,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1527
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1528 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 67 44 140 26 288 68 145 273), lower := (rows 35 67 44 140 26 288 68 128 256), losses := [] }

theorem u1528 : Upper (D 5) (R 5) [34,65,40,132,10,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1528
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1529 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 44 140 26 288 80 133 261), lower := (rows 35 67 44 140 26 288 80 128 256), losses := [] }

theorem u1529 : Upper (D 5) (R 5) [34,65,40,132,10,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1529
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1530 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 152 22 288 65 140 268), lower := (rows 35 67 44 152 22 288 65 128 256), losses := [] }

theorem u1530 : Upper (D 5) (R 5) [34,65,40,144,6,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1530
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1531 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 67 44 152 22 288 68 137 265), lower := (rows 35 67 44 152 22 288 68 128 256), losses := [] }

theorem u1531 : Upper (D 5) (R 5) [34,65,40,144,6,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1531
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1532 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 44 152 22 288 72 133 261), lower := (rows 35 67 44 152 22 288 72 128 256), losses := [] }

theorem u1532 : Upper (D 5) (R 5) [34,65,40,144,6,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1532
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1533 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 308, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 52 137 28 288 66 140 268), lower := (rows 35 67 52 137 28 288 66 128 256), losses := [] }

theorem u1533 : Upper (D 5) (R 5) [34,65,48,129,12,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1533
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1534 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 427, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 52 137 28 288 68 138 266), lower := (rows 35 67 52 137 28 288 68 128 256), losses := [] }

theorem u1534 : Upper (D 5) (R 5) [34,65,48,129,12,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1534
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1535 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2)], upper := (rows 35 67 52 137 28 288 72 134 262), lower := (rows 35 67 52 137 28 288 72 128 256), losses := [] }

theorem u1535 : Upper (D 5) (R 5) [34,65,48,129,12,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1535
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1536 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 137 276 40 66 140 268), lower := (rows 35 67 52 137 276 40 66 128 256), losses := [] }

theorem u1536 : Upper (D 5) (R 5) [34,65,48,129,260,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1536
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1537 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 171, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 52 137 276 40 68 138 266), lower := (rows 35 67 52 137 276 40 68 128 256), losses := [] }

theorem u1537 : Upper (D 5) (R 5) [34,65,48,129,260,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1537
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1538 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 52 137 276 40 72 134 262), lower := (rows 35 67 52 137 276 40 72 128 256), losses := [] }

theorem u1538 : Upper (D 5) (R 5) [34,65,48,129,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1538
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1539 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 308, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 52 138 28 288 65 140 268), lower := (rows 35 67 52 138 28 288 65 128 256), losses := [] }

theorem u1539 : Upper (D 5) (R 5) [34,65,48,130,12,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1539
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1540 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 427, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 52 138 28 288 68 137 265), lower := (rows 35 67 52 138 28 288 68 128 256), losses := [] }

theorem u1540 : Upper (D 5) (R 5) [34,65,48,130,12,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1540
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1541 : PairBound 9 := { available := 5, camps := [], pairs := [(2,1)], upper := (rows 35 67 52 138 28 288 72 133 261), lower := (rows 35 67 52 138 28 288 72 128 256), losses := [{ target := 1, region := (rows 1 0 94 8 88 299 88 131 259), good := (rows 421 501 116 508 124 288 124 128 288) }] }

theorem u1541 : Upper (D 5) (R 5) [34,65,48,130,12,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1541
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1542 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 52 138 273 40 68 140 268), lower := (rows 35 67 52 138 273 40 68 128 256), losses := [] }

theorem u1542 : Upper (D 5) (R 5) [34,65,48,130,257,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1542
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1543 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 276, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 67 52 138 273 40 72 132 260), lower := (rows 35 67 52 138 273 40 72 128 256), losses := [] }

theorem u1543 : Upper (D 5) (R 5) [34,65,48,130,257,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1543
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1544 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 138 276 40 65 140 268), lower := (rows 35 67 52 138 276 40 65 128 256), losses := [] }

theorem u1544 : Upper (D 5) (R 5) [34,65,48,130,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1544
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1545 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 171, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 52 138 276 40 68 137 265), lower := (rows 35 67 52 138 276 40 68 128 256), losses := [] }

theorem u1545 : Upper (D 5) (R 5) [34,65,48,130,260,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1545
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1546 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 67 52 138 276 40 72 133 261), lower := (rows 35 67 52 138 276 40 72 128 256), losses := [] }

theorem u1546 : Upper (D 5) (R 5) [34,65,48,130,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1546
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1547 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 292, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 52 140 25 288 66 140 268), lower := (rows 35 67 52 140 25 288 66 128 256), losses := [] }

theorem u1547 : Upper (D 5) (R 5) [34,65,48,132,9,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1547
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1548 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 67 52 140 25 288 68 138 266), lower := (rows 35 67 52 140 25 288 68 128 256), losses := [] }

theorem u1548 : Upper (D 5) (R 5) [34,65,48,132,9,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1548
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1549 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 66, targets := 4 }], pairs := [(1,2)], upper := (rows 35 67 52 140 25 288 72 134 262), lower := (rows 35 67 52 140 25 288 72 128 256), losses := [] }

theorem u1549 : Upper (D 5) (R 5) [34,65,48,132,9,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1549
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1550 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 292, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 52 140 26 288 65 140 268), lower := (rows 35 67 52 140 26 288 65 128 256), losses := [] }

theorem u1550 : Upper (D 5) (R 5) [34,65,48,132,10,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1550
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1551 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 67 52 140 26 288 68 137 265), lower := (rows 35 67 52 140 26 288 68 128 256), losses := [] }

theorem u1551 : Upper (D 5) (R 5) [34,65,48,132,10,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1551
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1552 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 293, targets := 8 }], pairs := [(0,3)], upper := (rows 35 67 52 140 26 288 72 133 261), lower := (rows 35 67 52 140 26 288 72 128 256), losses := [] }

theorem u1552 : Upper (D 5) (R 5) [34,65,48,132,10,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1552
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1553 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 172, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 140 273 40 66 140 268), lower := (rows 35 67 52 140 273 40 66 128 256), losses := [] }

theorem u1553 : Upper (D 5) (R 5) [34,65,48,132,257,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1553
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1554 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 52 140 273 40 68 138 266), lower := (rows 35 67 52 140 273 40 68 128 256), losses := [] }

theorem u1554 : Upper (D 5) (R 5) [34,65,48,132,257,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1554
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1555 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 276, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 35 67 52 140 273 40 72 134 262), lower := (rows 35 67 52 140 273 40 72 128 256), losses := [] }

theorem u1555 : Upper (D 5) (R 5) [34,65,48,132,257,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1555
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1556 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 172, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 52 140 274 40 65 140 268), lower := (rows 35 67 52 140 274 40 65 128 256), losses := [] }

theorem u1556 : Upper (D 5) (R 5) [34,65,48,132,258,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1556
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1557 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 52 140 274 40 68 137 265), lower := (rows 35 67 52 140 274 40 68 128 256), losses := [] }

theorem u1557 : Upper (D 5) (R 5) [34,65,48,132,258,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1557
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1558 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 35 67 52 140 274 40 72 133 261), lower := (rows 35 67 52 140 274 40 72 128 256), losses := [] }

theorem u1558 : Upper (D 5) (R 5) [34,65,48,132,258,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1558
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1559 : PairBound 9 := { available := 48, camps := [], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 266 28 36 72 176 304), lower := (rows 35 67 133 266 28 36 72 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 20 52 95 180 308), good := (rows 490 74 508 330 508 500 72 128 256) }] }

theorem u1559 : Upper (D 5) (R 5) [34,65,129,258,12,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1559
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1559
end Delivery.IrregularNine14.P05
