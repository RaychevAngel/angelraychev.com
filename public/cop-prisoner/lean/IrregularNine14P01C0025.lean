import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0003

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1500 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 277 35 70 138 48 40 208 208 464), lower := (rows 277 35 70 138 48 40 64 128 256), losses := [] }

theorem u1500 : Upper (D 1) (R 1) [276,33,66,130,32,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1500
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1501 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 204, targets := 16 }], pairs := [(2,4)], upper := (rows 277 35 70 138 48 48 200 200 456), lower := (rows 277 35 70 138 48 48 64 128 256), losses := [] }

theorem u1501 : Upper (D 1) (R 1) [276,33,66,130,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1501
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1502 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 277 35 70 138 48 96 216 152 408), lower := (rows 277 35 70 138 48 96 64 128 256), losses := [] }

theorem u1502 : Upper (D 1) (R 1) [276,33,66,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1502
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1503 : PairBound 9 := { available := 88, camps := [], pairs := [(0,7)], upper := (rows 277 35 70 138 48 160 88 216 344), lower := (rows 277 35 70 138 48 160 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 50 32 72 0 264), good := (rows 277 51 86 351 48 48 64 0 256) }] }

theorem u1503 : Upper (D 1) (R 1) [276,33,66,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1503
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1504 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 277 35 70 138 144 40 112 240 368), lower := (rows 277 35 70 138 144 40 64 128 256), losses := [] }

theorem u1504 : Upper (D 1) (R 1) [276,33,66,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1504
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1505 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 70 138 144 48 104 232 360), lower := (rows 277 35 70 138 144 48 64 128 256), losses := [] }

theorem u1505 : Upper (D 1) (R 1) [276,33,66,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1505
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1506 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 277 35 70 138 144 96 120 184 312), lower := (rows 277 35 70 138 144 96 64 128 256), losses := [] }

theorem u1506 : Upper (D 1) (R 1) [276,33,66,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1506
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1507 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 35 70 152 48 34 200 200 456), lower := (rows 277 35 70 152 48 34 64 128 256), losses := [] }

theorem u1507 : Upper (D 1) (R 1) [276,33,66,144,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1507
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1508 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 35 70 152 48 40 194 194 450), lower := (rows 277 35 70 152 48 40 64 128 256), losses := [] }

theorem u1508 : Upper (D 1) (R 1) [276,33,66,144,32,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1508
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1509 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 277 35 70 152 48 96 202 138 394), lower := (rows 277 35 70 152 48 96 64 128 256), losses := [] }

theorem u1509 : Upper (D 1) (R 1) [276,33,66,144,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1509
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1510 : PairBound 9 := { available := 74, camps := [{ cop := 5, region := 24, targets := 2 }], pairs := [(3,1)], upper := (rows 277 35 70 152 48 160 74 202 330), lower := (rows 277 35 70 152 48 160 64 128 256), losses := [] }

theorem u1510 : Upper (D 1) (R 1) [276,33,66,144,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1510
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1511 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 70 168 144 34 88 216 344), lower := (rows 277 35 70 168 144 34 64 128 256), losses := [] }

theorem u1511 : Upper (D 1) (R 1) [276,33,66,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1511
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1512 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 277 35 70 168 144 40 82 210 338), lower := (rows 277 35 70 168 144 40 64 128 256), losses := [] }

theorem u1512 : Upper (D 1) (R 1) [276,33,66,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1512
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1513 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 70 168 144 48 74 202 330), lower := (rows 277 35 70 168 144 48 64 128 256), losses := [] }

theorem u1513 : Upper (D 1) (R 1) [276,33,66,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1513
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1514 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 277 35 70 168 144 96 90 154 282), lower := (rows 277 35 70 168 144 96 64 128 256), losses := [] }

theorem u1514 : Upper (D 1) (R 1) [276,33,66,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1514
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1515 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 35 70 200 48 34 216 152 408), lower := (rows 277 35 70 200 48 34 64 128 256), losses := [] }

theorem u1515 : Upper (D 1) (R 1) [276,33,66,192,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1515
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1516 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 35 70 200 48 40 210 146 402), lower := (rows 277 35 70 200 48 40 64 128 256), losses := [] }

theorem u1516 : Upper (D 1) (R 1) [276,33,66,192,32,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1516
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1517 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 204, targets := 16 }], pairs := [(2,4)], upper := (rows 277 35 70 200 48 48 202 138 394), lower := (rows 277 35 70 200 48 48 64 128 256), losses := [] }

theorem u1517 : Upper (D 1) (R 1) [276,33,66,192,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1517
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1518 : Route 9 := (fun mask => (mask,id))

def c1518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1518 : Upper (D 1) (R 1) [276,33,66,192,32,128] 13 := by
  apply FastRouting.sound _ _ [276,33,66,192,32,128] 13 (by decide) (choices 1) [2,8,16] r1518 c1518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u190
  · exact u191
  · exact u192

def b1519 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 70 200 144 34 120 184 312), lower := (rows 277 35 70 200 144 34 64 128 256), losses := [] }

theorem u1519 : Upper (D 1) (R 1) [276,33,66,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1519
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1520 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 277 35 70 200 144 40 114 178 306), lower := (rows 277 35 70 200 144 40 64 128 256), losses := [] }

theorem u1520 : Upper (D 1) (R 1) [276,33,66,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1520
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1521 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 70 200 144 48 106 170 298), lower := (rows 277 35 70 200 144 48 64 128 256), losses := [] }

theorem u1521 : Upper (D 1) (R 1) [276,33,66,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1521
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1522 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 76 138 18 48 224 224 480), lower := (rows 277 35 76 138 18 48 64 128 256), losses := [] }

theorem u1522 : Upper (D 1) (R 1) [276,33,72,130,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1522
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1523 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 277 35 76 138 18 96 240 176 432), lower := (rows 277 35 76 138 18 96 64 128 256), losses := [] }

theorem u1523 : Upper (D 1) (R 1) [276,33,72,130,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1523
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1524 : PairBound 9 := { available := 112, camps := [], pairs := [(0,7)], upper := (rows 277 35 76 138 18 160 112 240 368), lower := (rows 277 35 76 138 18 160 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 26 32 66 0 258), good := (rows 277 371 93 351 338 32 64 0 256) }] }

theorem u1524 : Upper (D 1) (R 1) [276,33,72,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1524
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1525 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 76 138 48 34 208 208 464), lower := (rows 277 35 76 138 48 34 64 128 256), losses := [] }

theorem u1525 : Upper (D 1) (R 1) [276,33,72,130,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1525
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1526 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 204, targets := 16 }], pairs := [(2,4)], upper := (rows 277 35 76 138 48 48 194 194 450), lower := (rows 277 35 76 138 48 48 64 128 256), losses := [] }

theorem u1526 : Upper (D 1) (R 1) [276,33,72,130,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1526
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1527 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 277 35 76 138 48 96 210 146 402), lower := (rows 277 35 76 138 48 96 64 128 256), losses := [] }

theorem u1527 : Upper (D 1) (R 1) [276,33,72,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1527
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1528 : PairBound 9 := { available := 82, camps := [], pairs := [(0,7)], upper := (rows 277 35 76 138 48 160 82 210 338), lower := (rows 277 35 76 138 48 160 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 50 32 74 0 266), good := (rows 277 371 333 351 48 48 64 0 256) }] }

theorem u1528 : Upper (D 1) (R 1) [276,33,72,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1528
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1529 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 76 168 18 34 208 208 464), lower := (rows 277 35 76 168 18 34 64 128 256), losses := [] }

theorem u1529 : Upper (D 1) (R 1) [276,33,72,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1529
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1530 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 76 168 18 48 194 194 450), lower := (rows 277 35 76 168 18 48 64 128 256), losses := [] }

theorem u1530 : Upper (D 1) (R 1) [276,33,72,160,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1530
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1531 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 277 35 76 168 18 96 210 146 402), lower := (rows 277 35 76 168 18 96 64 128 256), losses := [] }

theorem u1531 : Upper (D 1) (R 1) [276,33,72,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1531
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1532 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 277 35 76 168 18 160 82 210 338), lower := (rows 277 35 76 168 18 160 64 128 256), losses := [] }

theorem u1532 : Upper (D 1) (R 1) [276,33,72,160,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1532
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1533 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 277 35 196 74 18 40 240 176 432), lower := (rows 277 35 196 74 18 40 64 128 256), losses := [] }

theorem u1533 : Upper (D 1) (R 1) [276,33,192,66,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1533
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1534 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 196 74 18 48 232 168 424), lower := (rows 277 35 196 74 18 48 64 128 256), losses := [] }

theorem u1534 : Upper (D 1) (R 1) [276,33,192,66,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1534
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1535 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 88, targets := 128 }], pairs := [(3,7)], upper := (rows 277 35 196 74 18 160 120 184 312), lower := (rows 277 35 196 74 18 160 64 128 256), losses := [] }

theorem u1535 : Upper (D 1) (R 1) [276,33,192,66,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1535
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1536 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 196 74 48 34 216 152 408), lower := (rows 277 35 196 74 48 34 64 128 256), losses := [] }

theorem u1536 : Upper (D 1) (R 1) [276,33,192,66,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1536
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1537 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 35 196 74 48 40 210 146 402), lower := (rows 277 35 196 74 48 40 64 128 256), losses := [] }

theorem u1537 : Upper (D 1) (R 1) [276,33,192,66,32,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1537
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1538 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 204, targets := 16 }], pairs := [(2,4)], upper := (rows 277 35 196 74 48 48 202 138 394), lower := (rows 277 35 196 74 48 48 64 128 256), losses := [] }

theorem u1538 : Upper (D 1) (R 1) [276,33,192,66,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1538
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1539 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 88, targets := 128 }], pairs := [(3,7)], upper := (rows 277 35 196 74 48 160 90 154 282), lower := (rows 277 35 196 74 48 160 64 128 256), losses := [] }

theorem u1539 : Upper (D 1) (R 1) [276,33,192,66,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1539
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1540 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 196 88 18 34 232 168 424), lower := (rows 277 35 196 88 18 34 64 128 256), losses := [] }

theorem u1540 : Upper (D 1) (R 1) [276,33,192,80,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1540
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1541 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 277 35 196 88 18 40 226 162 418), lower := (rows 277 35 196 88 18 40 64 128 256), losses := [] }

theorem u1541 : Upper (D 1) (R 1) [276,33,192,80,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1541
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1542 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 88, targets := 128 }], pairs := [(3,7)], upper := (rows 277 35 196 88 18 160 106 170 298), lower := (rows 277 35 196 88 18 160 64 128 256), losses := [] }

theorem u1542 : Upper (D 1) (R 1) [276,33,192,80,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1542
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1543 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 196 88 48 34 202 138 394), lower := (rows 277 35 196 88 48 34 64 128 256), losses := [] }

theorem u1543 : Upper (D 1) (R 1) [276,33,192,80,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1543
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1544 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 277 35 196 88 48 40 194 130 386), lower := (rows 277 35 196 88 48 40 64 128 256), losses := [] }

theorem u1544 : Upper (D 1) (R 1) [276,33,192,80,32,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1544
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1545 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 88, targets := 128 }], pairs := [(3,7)], upper := (rows 277 35 196 88 48 160 74 138 266), lower := (rows 277 35 196 88 48 160 64 128 256), losses := [] }

theorem u1545 : Upper (D 1) (R 1) [276,33,192,80,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1545
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1546 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 196 104 18 34 216 152 408), lower := (rows 277 35 196 104 18 34 64 128 256), losses := [] }

theorem u1546 : Upper (D 1) (R 1) [276,33,192,96,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1546
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1547 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 35 196 104 18 40 210 146 402), lower := (rows 277 35 196 104 18 40 64 128 256), losses := [] }

theorem u1547 : Upper (D 1) (R 1) [276,33,192,96,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1547
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1548 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 196 104 18 48 202 138 394), lower := (rows 277 35 196 104 18 48 64 128 256), losses := [] }

theorem u1548 : Upper (D 1) (R 1) [276,33,192,96,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1548
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1549 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 277 35 196 104 18 160 90 154 282), lower := (rows 277 35 196 104 18 160 64 128 256), losses := [] }

theorem u1549 : Upper (D 1) (R 1) [276,33,192,96,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1549
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1550 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 7 200 48 34 208 208 464), lower := (rows 277 42 7 200 48 34 64 128 256), losses := [] }

theorem u1550 : Upper (D 1) (R 1) [276,40,3,192,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1550
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1551 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 277 42 7 200 48 48 194 194 450), lower := (rows 277 42 7 200 48 48 64 128 256), losses := [] }

theorem u1551 : Upper (D 1) (R 1) [276,40,3,192,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1551
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1552 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 277 42 7 200 48 96 210 146 402), lower := (rows 277 42 7 200 48 96 64 128 256), losses := [] }

theorem u1552 : Upper (D 1) (R 1) [276,40,3,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1552
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1553 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 7 200 80 34 240 176 432), lower := (rows 277 42 7 200 80 34 64 128 256), losses := [] }

theorem u1553 : Upper (D 1) (R 1) [276,40,3,192,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1553
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1554 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 7 200 80 48 226 162 418), lower := (rows 277 42 7 200 80 48 64 128 256), losses := [] }

theorem u1554 : Upper (D 1) (R 1) [276,40,3,192,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1554
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1555 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 277 42 7 200 80 160 114 178 306), lower := (rows 277 42 7 200 80 160 64 128 256), losses := [] }

theorem u1555 : Upper (D 1) (R 1) [276,40,3,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1555
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1556 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 453, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 69 138 48 34 208 208 464), lower := (rows 277 42 69 138 48 34 64 128 256), losses := [] }

theorem u1556 : Upper (D 1) (R 1) [276,40,65,130,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1556
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1557 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 277 42 69 138 48 48 194 194 450), lower := (rows 277 42 69 138 48 48 64 128 256), losses := [] }

theorem u1557 : Upper (D 1) (R 1) [276,40,65,130,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1557
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1558 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 138, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 69 138 48 96 210 146 402), lower := (rows 277 42 69 138 48 96 64 128 256), losses := [] }

theorem u1558 : Upper (D 1) (R 1) [276,40,65,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1558
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1559 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 277 42 69 138 48 160 82 210 338), lower := (rows 277 42 69 138 48 160 64 128 256), losses := [] }

theorem u1559 : Upper (D 1) (R 1) [276,40,65,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1559
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1559
end Delivery.IrregularNine14.P01
