import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1560 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 268 44 50 96 80 193 321), lower := (rows 7 131 268 44 50 96 80 128 256), losses := [] }

theorem u1560 : Upper (D 6) (R 6) [6,129,264,36,34,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1560
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1561 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 44 81 96 66 176 304), lower := (rows 7 131 268 44 81 96 66 128 256), losses := [] }

theorem u1561 : Upper (D 6) (R 6) [6,129,264,36,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1561
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1562 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 268 44 81 96 80 162 290), lower := (rows 7 131 268 44 81 96 80 128 256), losses := [] }

theorem u1562 : Upper (D 6) (R 6) [6,129,264,36,65,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1562
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1563 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 44 81 96 96 146 274), lower := (rows 7 131 268 44 81 96 96 128 256), losses := [] }

theorem u1563 : Upper (D 6) (R 6) [6,129,264,36,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1563
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1564 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 44 82 96 65 176 304), lower := (rows 7 131 268 44 82 96 65 128 256), losses := [] }

theorem u1564 : Upper (D 6) (R 6) [6,129,264,36,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1564
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1565 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 268 44 82 96 80 161 289), lower := (rows 7 131 268 44 82 96 80 128 256), losses := [] }

theorem u1565 : Upper (D 6) (R 6) [6,129,264,36,66,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1565
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1566 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 44 82 96 96 145 273), lower := (rows 7 131 268 44 82 96 96 128 256), losses := [] }

theorem u1566 : Upper (D 6) (R 6) [6,129,264,36,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1566
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1567 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 268 56 82 36 65 224 352), lower := (rows 7 131 268 56 82 36 65 128 256), losses := [] }

theorem u1567 : Upper (D 6) (R 6) [6,129,264,48,66,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1567
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1568 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 131 268 56 82 36 96 193 321), lower := (rows 7 131 268 56 82 36 96 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 61 127 131 259), good := (rows 485 481 364 124 508 100 96 128 256) }] }

theorem u1568 : Upper (D 6) (R 6) [6,129,264,48,66,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1568
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1569 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 226, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,2),(4,0),(4,5)], upper := (rows 7 131 268 56 84 33 66 224 352), lower := (rows 7 131 268 56 84 33 66 128 256), losses := [] }

theorem u1569 : Upper (D 6) (R 6) [6,129,264,48,68,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1569
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1570 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 4, region := 131, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 7 131 268 56 84 33 96 194 322), lower := (rows 7 131 268 56 84 33 96 128 256), losses := [] }

theorem u1570 : Upper (D 6) (R 6) [6,129,264,48,68,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1570
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1571 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 34 },{ cop := 0, region := 226, targets := 4 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 131 268 56 84 34 65 224 352), lower := (rows 7 131 268 56 84 34 65 128 256), losses := [] }

theorem u1571 : Upper (D 6) (R 6) [6,129,264,48,68,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1571
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1572 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 120, targets := 1 },{ cop := 4, region := 131, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 131 268 56 84 34 96 193 321), lower := (rows 7 131 268 56 84 34 96 128 256), losses := [] }

theorem u1572 : Upper (D 6) (R 6) [6,129,264,48,68,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1572
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1573 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 104, targets := 2 },{ cop := 0, region := 48, targets := 64 }], pairs := [(3,1),(4,0),(4,6)], upper := (rows 7 131 268 104 50 36 65 208 336), lower := (rows 7 131 268 104 50 36 65 128 256), losses := [] }

theorem u1573 : Upper (D 6) (R 6) [6,129,264,96,34,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1573
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1574 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 391, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 268 104 50 36 80 193 321), lower := (rows 7 131 268 104 50 36 80 128 256), losses := [] }

theorem u1574 : Upper (D 6) (R 6) [6,129,264,96,34,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1574
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1575 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 0, region := 112, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 25 50 96 68 200 328), lower := (rows 7 131 292 25 50 96 68 128 256), losses := [] }

theorem u1575 : Upper (D 6) (R 6) [6,129,288,17,34,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1575
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1576 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 120, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 131 292 25 50 96 72 196 324), lower := (rows 7 131 292 25 50 96 72 128 256), losses := [] }

theorem u1576 : Upper (D 6) (R 6) [6,129,288,17,34,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1576
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1577 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 3, region := 356, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 131 292 25 82 96 68 168 296), lower := (rows 7 131 292 25 82 96 68 128 256), losses := [] }

theorem u1577 : Upper (D 6) (R 6) [6,129,288,17,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1577
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1578 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 292 25 82 96 72 164 292), lower := (rows 7 131 292 25 82 96 72 128 256), losses := [] }

theorem u1578 : Upper (D 6) (R 6) [6,129,288,17,66,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1578
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1579 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 3, region := 356, targets := 1 }], pairs := [(2,0),(3,2),(4,2)], upper := (rows 7 131 292 25 82 96 96 140 268), lower := (rows 7 131 292 25 82 96 96 128 256), losses := [] }

theorem u1579 : Upper (D 6) (R 6) [6,129,288,17,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1579
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1580 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 131 292 25 84 40 66 224 352), lower := (rows 7 131 292 25 84 40 66 128 256), losses := [] }

theorem u1580 : Upper (D 6) (R 6) [6,129,288,17,68,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1580
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1581 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 292 25 84 40 96 194 322), lower := (rows 7 131 292 25 84 40 96 128 256), losses := [] }

theorem u1581 : Upper (D 6) (R 6) [6,129,288,17,68,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1581
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1582 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 80, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 131 292 25 84 96 66 168 296), lower := (rows 7 131 292 25 84 96 66 128 256), losses := [] }

theorem u1582 : Upper (D 6) (R 6) [6,129,288,17,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1582
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1583 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 292 25 84 96 72 162 290), lower := (rows 7 131 292 25 84 96 72 128 256), losses := [] }

theorem u1583 : Upper (D 6) (R 6) [6,129,288,17,68,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1583
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1584 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 131 292 25 84 96 96 138 266), lower := (rows 7 131 292 25 84 96 96 128 256), losses := [] }

theorem u1584 : Upper (D 6) (R 6) [6,129,288,17,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1584
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1585 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 7 131 292 25 112 34 68 200 328), lower := (rows 7 131 292 25 112 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 31 35 77 136 264), good := (rows 118 242 372 508 112 50 84 128 256) }] }

theorem u1585 : Upper (D 6) (R 6) [6,129,288,17,96,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1585
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1586 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 120, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 131 292 25 112 34 72 196 324), lower := (rows 7 131 292 25 112 34 72 128 256), losses := [] }

theorem u1586 : Upper (D 6) (R 6) [6,129,288,17,96,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1586
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1587 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 0, region := 112, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 131 292 26 49 96 68 200 328), lower := (rows 7 131 292 26 49 96 68 128 256), losses := [] }

theorem u1587 : Upper (D 6) (R 6) [6,129,288,18,33,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1587
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1588 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 120, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 131 292 26 49 96 72 196 324), lower := (rows 7 131 292 26 49 96 72 128 256), losses := [] }

theorem u1588 : Upper (D 6) (R 6) [6,129,288,18,33,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1588
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1589 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 3, region := 356, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 131 292 26 81 96 68 168 296), lower := (rows 7 131 292 26 81 96 68 128 256), losses := [] }

theorem u1589 : Upper (D 6) (R 6) [6,129,288,18,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1589
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1590 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 292 26 81 96 72 164 292), lower := (rows 7 131 292 26 81 96 72 128 256), losses := [] }

theorem u1590 : Upper (D 6) (R 6) [6,129,288,18,65,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1590
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1591 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 3, region := 356, targets := 1 }], pairs := [(2,0),(3,2),(4,2)], upper := (rows 7 131 292 26 81 96 96 140 268), lower := (rows 7 131 292 26 81 96 96 128 256), losses := [] }

theorem u1591 : Upper (D 6) (R 6) [6,129,288,18,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1591
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1592 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 131 292 26 84 40 65 224 352), lower := (rows 7 131 292 26 84 40 65 128 256), losses := [] }

theorem u1592 : Upper (D 6) (R 6) [6,129,288,18,68,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1592
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1593 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 292 26 84 40 96 193 321), lower := (rows 7 131 292 26 84 40 96 128 256), losses := [] }

theorem u1593 : Upper (D 6) (R 6) [6,129,288,18,68,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1593
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1594 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 131 292 26 84 96 65 168 296), lower := (rows 7 131 292 26 84 96 65 128 256), losses := [] }

theorem u1594 : Upper (D 6) (R 6) [6,129,288,18,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1594
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1595 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 292 26 84 96 72 161 289), lower := (rows 7 131 292 26 84 96 72 128 256), losses := [] }

theorem u1595 : Upper (D 6) (R 6) [6,129,288,18,68,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1595
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1596 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 131 292 26 84 96 96 137 265), lower := (rows 7 131 292 26 84 96 96 128 256), losses := [] }

theorem u1596 : Upper (D 6) (R 6) [6,129,288,18,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1596
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1597 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 7 131 292 28 49 96 66 200 328), lower := (rows 7 131 292 28 49 96 66 128 256), losses := [] }

theorem u1597 : Upper (D 6) (R 6) [6,129,288,20,33,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1597
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1598 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 120, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 131 292 28 49 96 72 194 322), lower := (rows 7 131 292 28 49 96 72 128 256), losses := [] }

theorem u1598 : Upper (D 6) (R 6) [6,129,288,20,33,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1598
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1599 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 7 131 292 28 50 96 65 200 328), lower := (rows 7 131 292 28 50 96 65 128 256), losses := [] }

theorem u1599 : Upper (D 6) (R 6) [6,129,288,20,34,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1599
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1600 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 292 28 50 96 72 193 321), lower := (rows 7 131 292 28 50 96 72 128 256), losses := [] }

theorem u1600 : Upper (D 6) (R 6) [6,129,288,20,34,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1600
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1601 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 88, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 131 292 28 81 34 72 224 352), lower := (rows 7 131 292 28 81 34 72 128 256), losses := [] }

theorem u1601 : Upper (D 6) (R 6) [6,129,288,20,65,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1601
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1602 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(2,0),(3,0),(4,2)], upper := (rows 7 131 292 28 81 34 96 200 328), lower := (rows 7 131 292 28 81 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 119 152 280), good := (rows 102 226 356 476 508 98 96 128 256) }] }

theorem u1602 : Upper (D 6) (R 6) [6,129,288,20,65,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1602
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1603 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 28 81 40 66 224 352), lower := (rows 7 131 292 28 81 40 66 128 256), losses := [] }

theorem u1603 : Upper (D 6) (R 6) [6,129,288,20,65,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1603
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1604 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 120, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 131 292 28 81 40 96 194 322), lower := (rows 7 131 292 28 81 40 96 128 256), losses := [] }

theorem u1604 : Upper (D 6) (R 6) [6,129,288,20,65,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1604
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1605 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 292 28 81 96 66 168 296), lower := (rows 7 131 292 28 81 96 66 128 256), losses := [] }

theorem u1605 : Upper (D 6) (R 6) [6,129,288,20,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1605
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1606 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 292 28 81 96 72 162 290), lower := (rows 7 131 292 28 81 96 72 128 256), losses := [] }

theorem u1606 : Upper (D 6) (R 6) [6,129,288,20,65,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1606
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1607 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 131 292 28 81 96 96 138 266), lower := (rows 7 131 292 28 81 96 96 128 256), losses := [] }

theorem u1607 : Upper (D 6) (R 6) [6,129,288,20,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1607
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1608 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 28 82 40 65 224 352), lower := (rows 7 131 292 28 82 40 65 128 256), losses := [] }

theorem u1608 : Upper (D 6) (R 6) [6,129,288,20,66,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1608
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1609 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 292 28 82 40 96 193 321), lower := (rows 7 131 292 28 82 40 96 128 256), losses := [] }

theorem u1609 : Upper (D 6) (R 6) [6,129,288,20,66,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1609
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1610 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 292 28 82 96 65 168 296), lower := (rows 7 131 292 28 82 96 65 128 256), losses := [] }

theorem u1610 : Upper (D 6) (R 6) [6,129,288,20,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1610
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1611 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 292 28 82 96 72 161 289), lower := (rows 7 131 292 28 82 96 72 128 256), losses := [] }

theorem u1611 : Upper (D 6) (R 6) [6,129,288,20,66,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1611
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1612 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 131 292 28 82 96 96 137 265), lower := (rows 7 131 292 28 82 96 96 128 256), losses := [] }

theorem u1612 : Upper (D 6) (R 6) [6,129,288,20,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1612
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1613 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 88, targets := 1 },{ cop := 0, region := 88, targets := 32 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 7 131 292 28 88 33 66 224 352), lower := (rows 7 131 292 28 88 33 66 128 256), losses := [] }

theorem u1613 : Upper (D 6) (R 6) [6,129,288,20,72,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1613
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1614 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 131 292 28 88 33 96 194 322), lower := (rows 7 131 292 28 88 33 96 128 256), losses := [] }

theorem u1614 : Upper (D 6) (R 6) [6,129,288,20,72,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1614
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1615 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 88, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 131 292 28 88 34 65 224 352), lower := (rows 7 131 292 28 88 34 65 128 256), losses := [] }

theorem u1615 : Upper (D 6) (R 6) [6,129,288,20,72,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1615
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1616 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 131 292 28 88 34 96 193 321), lower := (rows 7 131 292 28 88 34 96 128 256), losses := [] }

theorem u1616 : Upper (D 6) (R 6) [6,129,288,20,72,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1616
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1617 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 268, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 292 28 112 34 65 200 328), lower := (rows 7 131 292 28 112 34 65 128 256), losses := [] }

theorem u1617 : Upper (D 6) (R 6) [6,129,288,20,96,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1617
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1618 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 131 292 28 112 34 72 193 321), lower := (rows 7 131 292 28 112 34 72 128 256), losses := [] }

theorem u1618 : Upper (D 6) (R 6) [6,129,288,20,96,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1618
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1619 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 0, region := 80, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 292 41 82 96 68 152 280), lower := (rows 7 131 292 41 82 96 68 128 256), losses := [] }

theorem u1619 : Upper (D 6) (R 6) [6,129,288,33,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1619
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1619
end Delivery.IrregularNine14.P06
