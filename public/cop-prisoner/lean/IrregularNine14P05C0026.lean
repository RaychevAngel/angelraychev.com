import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1560 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 99, targets := 8 }], pairs := [(0,3)], upper := (rows 35 67 133 266 28 36 80 168 296), lower := (rows 35 67 133 266 28 36 80 128 256), losses := [] }

theorem u1560 : Upper (D 5) (R 5) [34,65,129,258,12,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1560
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1561 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 133 266 28 36 96 152 280), lower := (rows 35 67 133 266 28 36 96 128 256), losses := [] }

theorem u1561 : Upper (D 5) (R 5) [34,65,129,258,12,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1561
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1562 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 35 67 133 266 28 40 68 176 304), lower := (rows 35 67 133 266 28 40 68 128 256), losses := [] }

theorem u1562 : Upper (D 5) (R 5) [34,65,129,258,12,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1562
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1563 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 133 266 28 40 80 164 292), lower := (rows 35 67 133 266 28 40 80 128 256), losses := [] }

theorem u1563 : Upper (D 5) (R 5) [34,65,129,258,12,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1563
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1564 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 133 266 28 40 96 148 276), lower := (rows 35 67 133 266 28 40 96 128 256), losses := [] }

theorem u1564 : Upper (D 5) (R 5) [34,65,129,258,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1564
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1565 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3)], upper := (rows 35 67 133 266 28 48 68 168 296), lower := (rows 35 67 133 266 28 48 68 128 256), losses := [] }

theorem u1565 : Upper (D 5) (R 5) [34,65,129,258,12,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1565
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1566 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 133 266 28 48 72 164 292), lower := (rows 35 67 133 266 28 48 72 128 256), losses := [] }

theorem u1566 : Upper (D 5) (R 5) [34,65,129,258,12,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1566
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1567 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 99, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 133 266 28 48 96 140 268), lower := (rows 35 67 133 266 28 48 96 128 256), losses := [] }

theorem u1567 : Upper (D 5) (R 5) [34,65,129,258,12,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1567
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1568 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 66, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 35 67 133 266 52 40 68 152 280), lower := (rows 35 67 133 266 52 40 68 128 256), losses := [] }

theorem u1568 : Upper (D 5) (R 5) [34,65,129,258,36,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1568
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1569 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 148, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 67 133 266 52 40 72 148 276), lower := (rows 35 67 133 266 52 40 72 128 256), losses := [] }

theorem u1569 : Upper (D 5) (R 5) [34,65,129,258,36,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1569
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1570 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 67, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 133 266 52 40 80 140 268), lower := (rows 35 67 133 266 52 40 80 128 256), losses := [] }

theorem u1570 : Upper (D 5) (R 5) [34,65,129,258,36,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1570
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1571 : PairBound 9 := { available := 24, camps := [{ cop := 7, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 133 266 56 36 68 152 280), lower := (rows 35 67 133 266 56 36 68 128 256), losses := [] }

theorem u1571 : Upper (D 5) (R 5) [34,65,129,258,40,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1571
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1572 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 67, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 133 266 56 36 72 148 276), lower := (rows 35 67 133 266 56 36 72 128 256), losses := [] }

theorem u1572 : Upper (D 5) (R 5) [34,65,129,258,40,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1572
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1573 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 67, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 133 266 56 36 80 140 268), lower := (rows 35 67 133 266 56 36 80 128 256), losses := [] }

theorem u1573 : Upper (D 5) (R 5) [34,65,129,258,40,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1573
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1574 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 35 67 133 268 26 40 68 176 304), lower := (rows 35 67 133 268 26 40 68 128 256), losses := [] }

theorem u1574 : Upper (D 5) (R 5) [34,65,129,260,10,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1574
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1575 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 115, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 133 268 26 40 80 164 292), lower := (rows 35 67 133 268 26 40 80 128 256), losses := [] }

theorem u1575 : Upper (D 5) (R 5) [34,65,129,260,10,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1575
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1576 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 133 268 26 40 96 148 276), lower := (rows 35 67 133 268 26 40 96 128 256), losses := [] }

theorem u1576 : Upper (D 5) (R 5) [34,65,129,260,10,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1576
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1577 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 280 52 40 66 140 268), lower := (rows 35 67 133 280 52 40 66 128 256), losses := [] }

theorem u1577 : Upper (D 5) (R 5) [34,65,129,272,36,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1577
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1578 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 66, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 35 67 133 280 52 40 68 138 266), lower := (rows 35 67 133 280 52 40 68 128 256), losses := [] }

theorem u1578 : Upper (D 5) (R 5) [34,65,129,272,36,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1578
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1579 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 148, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 35 67 133 280 52 40 72 134 262), lower := (rows 35 67 133 280 52 40 72 128 256), losses := [] }

theorem u1579 : Upper (D 5) (R 5) [34,65,129,272,36,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1579
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1580 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 280 56 36 66 140 268), lower := (rows 35 67 133 280 56 36 66 128 256), losses := [] }

theorem u1580 : Upper (D 5) (R 5) [34,65,129,272,40,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1580
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1581 : PairBound 9 := { available := 10, camps := [{ cop := 7, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 133 280 56 36 68 138 266), lower := (rows 35 67 133 280 56 36 68 128 256), losses := [] }

theorem u1581 : Upper (D 5) (R 5) [34,65,129,272,40,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1581
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1582 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 167, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 133 280 56 36 72 134 262), lower := (rows 35 67 133 280 56 36 72 128 256), losses := [] }

theorem u1582 : Upper (D 5) (R 5) [34,65,129,272,40,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1582
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1583 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 312, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 296 28 48 66 140 268), lower := (rows 35 67 133 296 28 48 66 128 256), losses := [] }

theorem u1583 : Upper (D 5) (R 5) [34,65,129,288,12,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1583
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1584 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3)], upper := (rows 35 67 133 296 28 48 68 138 266), lower := (rows 35 67 133 296 28 48 68 128 256), losses := [] }

theorem u1584 : Upper (D 5) (R 5) [34,65,129,288,12,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1584
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1585 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 132, targets := 8 }], pairs := [(2,3)], upper := (rows 35 67 133 296 28 48 72 134 262), lower := (rows 35 67 133 296 28 48 72 128 256), losses := [] }

theorem u1585 : Upper (D 5) (R 5) [34,65,129,288,12,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1585
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1586 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 66, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 67 134 268 25 36 72 176 304), lower := (rows 35 67 134 268 25 36 72 128 256), losses := [] }

theorem u1586 : Upper (D 5) (R 5) [34,65,130,260,9,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1586
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1587 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 66, targets := 4 }], pairs := [(1,2)], upper := (rows 35 67 134 268 25 36 80 168 296), lower := (rows 35 67 134 268 25 36 80 128 256), losses := [] }

theorem u1587 : Upper (D 5) (R 5) [34,65,130,260,9,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1587
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1588 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 134 268 25 36 96 152 280), lower := (rows 35 67 134 268 25 36 96 128 256), losses := [] }

theorem u1588 : Upper (D 5) (R 5) [34,65,130,260,9,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1588
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1589 : PairBound 9 := { available := 48, camps := [], pairs := [(3,1),(4,1)], upper := (rows 35 67 134 268 25 40 68 176 304), lower := (rows 35 67 134 268 25 40 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 76 18 126 76 151 279), good := (rows 433 505 508 492 505 104 492 128 256) }] }

theorem u1589 : Upper (D 5) (R 5) [34,65,130,260,9,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1589
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1590 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 115, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 134 268 25 40 80 164 292), lower := (rows 35 67 134 268 25 40 80 128 256), losses := [] }

theorem u1590 : Upper (D 5) (R 5) [34,65,130,260,9,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1590
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1591 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 134 268 25 40 96 148 276), lower := (rows 35 67 134 268 25 40 96 128 256), losses := [] }

theorem u1591 : Upper (D 5) (R 5) [34,65,130,260,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1591
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1592 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 134 280 28 36 65 168 296), lower := (rows 35 67 134 280 28 36 65 128 256), losses := [] }

theorem u1592 : Upper (D 5) (R 5) [34,65,130,272,12,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1592
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1593 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 167, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 134 280 28 36 72 161 289), lower := (rows 35 67 134 280 28 36 72 128 256), losses := [] }

theorem u1593 : Upper (D 5) (R 5) [34,65,130,272,12,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1593
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1594 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 134 280 28 36 96 137 265), lower := (rows 35 67 134 280 28 36 96 128 256), losses := [] }

theorem u1594 : Upper (D 5) (R 5) [34,65,130,272,12,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1594
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1595 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 134 280 52 40 65 140 268), lower := (rows 35 67 134 280 52 40 65 128 256), losses := [] }

theorem u1595 : Upper (D 5) (R 5) [34,65,130,272,36,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1595
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1596 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 134 280 52 40 68 137 265), lower := (rows 35 67 134 280 52 40 68 128 256), losses := [] }

theorem u1596 : Upper (D 5) (R 5) [34,65,130,272,36,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1596
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1597 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 148, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 35 67 134 280 52 40 72 133 261), lower := (rows 35 67 134 280 52 40 72 128 256), losses := [] }

theorem u1597 : Upper (D 5) (R 5) [34,65,130,272,36,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1597
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1598 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 134 280 56 36 65 140 268), lower := (rows 35 67 134 280 56 36 65 128 256), losses := [] }

theorem u1598 : Upper (D 5) (R 5) [34,65,130,272,40,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1598
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1599 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 67 134 280 56 36 68 137 265), lower := (rows 35 67 134 280 56 36 68 128 256), losses := [] }

theorem u1599 : Upper (D 5) (R 5) [34,65,130,272,40,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1599
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1600 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 167, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 134 280 56 36 72 133 261), lower := (rows 35 67 134 280 56 36 72 128 256), losses := [] }

theorem u1600 : Upper (D 5) (R 5) [34,65,130,272,40,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1600
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1601 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 134 296 28 36 65 152 280), lower := (rows 35 67 134 296 28 36 65 128 256), losses := [] }

theorem u1601 : Upper (D 5) (R 5) [34,65,130,288,12,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1601
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1602 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 134 296 28 36 72 145 273), lower := (rows 35 67 134 296 28 36 72 128 256), losses := [] }

theorem u1602 : Upper (D 5) (R 5) [34,65,130,288,12,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1602
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1603 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 2 }], pairs := [(3,1)], upper := (rows 35 67 134 296 28 36 80 137 265), lower := (rows 35 67 134 296 28 36 80 128 256), losses := [] }

theorem u1603 : Upper (D 5) (R 5) [34,65,130,288,12,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1603
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1604 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 312, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 134 296 28 48 65 140 268), lower := (rows 35 67 134 296 28 48 65 128 256), losses := [] }

theorem u1604 : Upper (D 5) (R 5) [34,65,130,288,12,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1604
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1605 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 2 }], pairs := [(3,1)], upper := (rows 35 67 134 296 28 48 68 137 265), lower := (rows 35 67 134 296 28 48 68 128 256), losses := [] }

theorem u1605 : Upper (D 5) (R 5) [34,65,130,288,12,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1605
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1606 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 8 }], pairs := [(2,3)], upper := (rows 35 67 134 296 28 48 72 133 261), lower := (rows 35 67 134 296 28 48 72 128 256), losses := [] }

theorem u1606 : Upper (D 5) (R 5) [34,65,130,288,12,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1606
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1607 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 140 280 21 36 66 168 296), lower := (rows 35 67 140 280 21 36 66 128 256), losses := [] }

theorem u1607 : Upper (D 5) (R 5) [34,65,136,272,5,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1607
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1608 : PairBound 9 := { available := 34, camps := [], pairs := [(2,0),(3,0)], upper := (rows 35 67 140 280 21 36 72 162 290), lower := (rows 35 67 140 280 21 36 72 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 60 92 129 257), good := (rows 418 450 236 380 508 100 104 128 256) }] }

theorem u1608 : Upper (D 5) (R 5) [34,65,136,272,5,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1608
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1609 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 280 21 36 96 138 266), lower := (rows 35 67 140 280 21 36 96 128 256), losses := [] }

theorem u1609 : Upper (D 5) (R 5) [34,65,136,272,5,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1609
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1610 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 140 280 21 40 66 164 292), lower := (rows 35 67 140 280 21 40 66 128 256), losses := [] }

theorem u1610 : Upper (D 5) (R 5) [34,65,136,272,5,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1610
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1611 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 66, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 35 67 140 280 21 40 68 162 290), lower := (rows 35 67 140 280 21 40 68 128 256), losses := [] }

theorem u1611 : Upper (D 5) (R 5) [34,65,136,272,5,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1611
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1612 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 280 21 40 96 134 262), lower := (rows 35 67 140 280 21 40 96 128 256), losses := [] }

theorem u1612 : Upper (D 5) (R 5) [34,65,136,272,5,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1612
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1613 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 140 280 22 36 65 168 296), lower := (rows 35 67 140 280 22 36 65 128 256), losses := [] }

theorem u1613 : Upper (D 5) (R 5) [34,65,136,272,6,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1613
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1614 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 33, targets := 8 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 280 22 36 72 161 289), lower := (rows 35 67 140 280 22 36 72 128 256), losses := [{ target := 2, region := (rows 33 34 0 8 16 32 76 161 289), good := (rows 419 451 200 344 82 483 72 128 256) }] }

theorem u1614 : Upper (D 5) (R 5) [34,65,136,272,6,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1614
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1615 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 280 22 36 96 137 265), lower := (rows 35 67 140 280 22 36 96 128 256), losses := [] }

theorem u1615 : Upper (D 5) (R 5) [34,65,136,272,6,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1615
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1616 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 140 280 22 40 65 164 292), lower := (rows 35 67 140 280 22 40 65 128 256), losses := [] }

theorem u1616 : Upper (D 5) (R 5) [34,65,136,272,6,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1616
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1617 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 297, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 67 140 280 22 40 68 161 289), lower := (rows 35 67 140 280 22 40 68 128 256), losses := [] }

theorem u1617 : Upper (D 5) (R 5) [34,65,136,272,6,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1617
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1618 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 280 22 40 96 133 261), lower := (rows 35 67 140 280 22 40 96 128 256), losses := [] }

theorem u1618 : Upper (D 5) (R 5) [34,65,136,272,6,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1618
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1619 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 140 296 21 36 66 152 280), lower := (rows 35 67 140 296 21 36 66 128 256), losses := [] }

theorem u1619 : Upper (D 5) (R 5) [34,65,136,288,5,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1619
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1619
end Delivery.IrregularNine14.P05
