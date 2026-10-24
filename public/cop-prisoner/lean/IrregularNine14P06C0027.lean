import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1620 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 120, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 131 292 41 82 96 72 148 276), lower := (rows 7 131 292 41 82 96 72 128 256), losses := [] }

theorem u1620 : Upper (D 6) (R 6) [6,129,288,33,66,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1620
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1621 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 292 41 82 96 80 140 268), lower := (rows 7 131 292 41 82 96 80 128 256), losses := [] }

theorem u1621 : Upper (D 6) (R 6) [6,129,288,33,66,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1621
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1622 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 104, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,0),(4,5)], upper := (rows 7 131 292 41 84 96 66 152 280), lower := (rows 7 131 292 41 84 96 66 128 256), losses := [] }

theorem u1622 : Upper (D 6) (R 6) [6,129,288,33,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1622
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1623 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 131, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 7 131 292 41 84 96 72 146 274), lower := (rows 7 131 292 41 84 96 72 128 256), losses := [] }

theorem u1623 : Upper (D 6) (R 6) [6,129,288,33,68,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1623
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1624 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 292 41 84 96 80 138 266), lower := (rows 7 131 292 41 84 96 80 128 256), losses := [] }

theorem u1624 : Upper (D 6) (R 6) [6,129,288,33,68,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1624
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1625 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 4, region := 292, targets := 1 }], pairs := [(2,0),(3,2),(4,2)], upper := (rows 7 131 292 41 88 96 66 148 276), lower := (rows 7 131 292 41 88 96 66 128 256), losses := [] }

theorem u1625 : Upper (D 6) (R 6) [6,129,288,33,72,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1625
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1626 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(3,1),(4,1)], upper := (rows 7 131 292 41 88 96 68 146 274), lower := (rows 7 131 292 41 88 96 68 128 256), losses := [] }

theorem u1626 : Upper (D 6) (R 6) [6,129,288,33,72,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1626
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1627 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 120, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 131 292 41 88 96 80 134 262), lower := (rows 7 131 292 41 88 96 80 128 256), losses := [] }

theorem u1627 : Upper (D 6) (R 6) [6,129,288,33,72,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1627
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1628 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 170, targets := 4 },{ cop := 8, region := 100, targets := 1 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 131 292 42 81 96 68 152 280), lower := (rows 7 131 292 42 81 96 68 128 256), losses := [] }

theorem u1628 : Upper (D 6) (R 6) [6,129,288,34,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1628
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1629 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 120, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 131 292 42 81 96 72 148 276), lower := (rows 7 131 292 42 81 96 72 128 256), losses := [] }

theorem u1629 : Upper (D 6) (R 6) [6,129,288,34,65,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1629
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1630 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 292 42 81 96 80 140 268), lower := (rows 7 131 292 42 81 96 80 128 256), losses := [] }

theorem u1630 : Upper (D 6) (R 6) [6,129,288,34,65,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1630
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1631 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,1),(4,5)], upper := (rows 7 131 292 42 84 48 65 200 328), lower := (rows 7 131 292 42 84 48 65 128 256), losses := [] }

theorem u1631 : Upper (D 6) (R 6) [6,129,288,34,68,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1631
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1632 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0)], upper := (rows 7 131 292 42 84 48 72 193 321), lower := (rows 7 131 292 42 84 48 72 128 256), losses := [] }

theorem u1632 : Upper (D 6) (R 6) [6,129,288,34,68,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1632
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1633 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 104, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,1),(4,5)], upper := (rows 7 131 292 42 84 96 65 152 280), lower := (rows 7 131 292 42 84 96 65 128 256), losses := [] }

theorem u1633 : Upper (D 6) (R 6) [6,129,288,34,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1633
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1634 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 131, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 7 131 292 42 84 96 72 145 273), lower := (rows 7 131 292 42 84 96 72 128 256), losses := [] }

theorem u1634 : Upper (D 6) (R 6) [6,129,288,34,68,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1634
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1635 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 292 42 84 96 80 137 265), lower := (rows 7 131 292 42 84 96 80 128 256), losses := [] }

theorem u1635 : Upper (D 6) (R 6) [6,129,288,34,68,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1635
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1636 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 4, region := 292, targets := 1 }], pairs := [(2,0),(3,2),(4,2)], upper := (rows 7 131 292 42 88 96 65 148 276), lower := (rows 7 131 292 42 88 96 65 128 256), losses := [] }

theorem u1636 : Upper (D 6) (R 6) [6,129,288,34,72,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1636
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1637 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 120, targets := 1 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 131 292 42 88 96 68 145 273), lower := (rows 7 131 292 42 88 96 68 128 256), losses := [] }

theorem u1637 : Upper (D 6) (R 6) [6,129,288,34,72,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1637
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1638 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 120, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 131 292 42 88 96 80 133 261), lower := (rows 7 131 292 42 88 96 80 128 256), losses := [] }

theorem u1638 : Upper (D 6) (R 6) [6,129,288,34,72,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1638
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1639 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 80, targets := 34 }], pairs := [(2,0),(4,1),(4,5)], upper := (rows 7 131 292 56 84 34 65 200 328), lower := (rows 7 131 292 56 84 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 76 72 80 35 64 208 336), good := (rows 38 162 292 444 476 34 508 128 256) }] }

theorem u1639 : Upper (D 6) (R 6) [6,129,288,48,68,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1639
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1640 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 131 292 56 84 34 72 193 321), lower := (rows 7 131 292 56 84 34 72 128 256), losses := [] }

theorem u1640 : Upper (D 6) (R 6) [6,129,288,48,68,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1640
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1641 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 2, region := 195, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 131 292 56 88 34 65 196 324), lower := (rows 7 131 292 56 88 34 65 128 256), losses := [] }

theorem u1641 : Upper (D 6) (R 6) [6,129,288,48,72,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1641
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1642 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 131 292 56 88 34 68 193 321), lower := (rows 7 131 292 56 88 34 68 128 256), losses := [] }

theorem u1642 : Upper (D 6) (R 6) [6,129,288,48,72,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1642
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1643 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 131 292 73 82 40 68 176 304), lower := (rows 7 131 292 73 82 40 68 128 256), losses := [] }

theorem u1643 : Upper (D 6) (R 6) [6,129,288,65,66,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1643
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1644 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 131 292 73 82 40 80 164 292), lower := (rows 7 131 292 73 82 40 80 128 256), losses := [] }

theorem u1644 : Upper (D 6) (R 6) [6,129,288,65,66,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1644
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1645 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 120, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 131 292 73 82 40 96 148 276), lower := (rows 7 131 292 73 82 40 96 128 256), losses := [] }

theorem u1645 : Upper (D 6) (R 6) [6,129,288,65,66,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1645
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1646 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 131 292 73 82 48 68 168 296), lower := (rows 7 131 292 73 82 48 68 128 256), losses := [] }

theorem u1646 : Upper (D 6) (R 6) [6,129,288,65,66,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1646
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1647 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 293, targets := 64 }], pairs := [(0,6)], upper := (rows 7 131 292 73 82 48 72 164 292), lower := (rows 7 131 292 73 82 48 72 128 256), losses := [] }

theorem u1647 : Upper (D 6) (R 6) [6,129,288,65,66,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1647
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1648 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 120, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 131 292 73 82 48 96 140 268), lower := (rows 7 131 292 73 82 48 96 128 256), losses := [] }

theorem u1648 : Upper (D 6) (R 6) [6,129,288,65,66,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1648
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1649 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 131 292 73 84 34 72 176 304), lower := (rows 7 131 292 73 84 34 72 128 256), losses := [] }

theorem u1649 : Upper (D 6) (R 6) [6,129,288,65,68,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1649
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1650 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 88, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 131 292 73 84 34 80 168 296), lower := (rows 7 131 292 73 84 34 80 128 256), losses := [] }

theorem u1650 : Upper (D 6) (R 6) [6,129,288,65,68,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1650
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1651 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 131 292 73 84 34 96 152 280), lower := (rows 7 131 292 73 84 34 96 128 256), losses := [] }

theorem u1651 : Upper (D 6) (R 6) [6,129,288,65,68,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1651
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1652 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 73 84 40 66 176 304), lower := (rows 7 131 292 73 84 40 66 128 256), losses := [] }

theorem u1652 : Upper (D 6) (R 6) [6,129,288,65,68,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1652
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1653 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 7 131 292 73 84 40 80 162 290), lower := (rows 7 131 292 73 84 40 80 128 256), losses := [] }

theorem u1653 : Upper (D 6) (R 6) [6,129,288,65,68,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1653
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1654 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 292 73 84 40 96 146 274), lower := (rows 7 131 292 73 84 40 96 128 256), losses := [] }

theorem u1654 : Upper (D 6) (R 6) [6,129,288,65,68,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1654
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1655 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 73 84 48 66 168 296), lower := (rows 7 131 292 73 84 48 66 128 256), losses := [] }

theorem u1655 : Upper (D 6) (R 6) [6,129,288,65,68,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1655
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1656 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 131 292 73 84 48 72 162 290), lower := (rows 7 131 292 73 84 48 72 128 256), losses := [] }

theorem u1656 : Upper (D 6) (R 6) [6,129,288,65,68,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1656
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1657 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 73 84 48 96 138 266), lower := (rows 7 131 292 73 84 48 96 128 256), losses := [] }

theorem u1657 : Upper (D 6) (R 6) [6,129,288,65,68,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1657
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1658 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 131 292 74 84 33 72 176 304), lower := (rows 7 131 292 74 84 33 72 128 256), losses := [] }

theorem u1658 : Upper (D 6) (R 6) [6,129,288,66,68,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1658
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1659 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 131 292 74 84 33 80 168 296), lower := (rows 7 131 292 74 84 33 80 128 256), losses := [] }

theorem u1659 : Upper (D 6) (R 6) [6,129,288,66,68,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1659
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1660 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 131 292 74 84 33 96 152 280), lower := (rows 7 131 292 74 84 33 96 128 256), losses := [] }

theorem u1660 : Upper (D 6) (R 6) [6,129,288,66,68,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1660
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1661 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 74 84 40 65 176 304), lower := (rows 7 131 292 74 84 40 65 128 256), losses := [] }

theorem u1661 : Upper (D 6) (R 6) [6,129,288,66,68,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1661
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1662 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 7 131 292 74 84 40 80 161 289), lower := (rows 7 131 292 74 84 40 80 128 256), losses := [] }

theorem u1662 : Upper (D 6) (R 6) [6,129,288,66,68,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1662
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1663 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 292 74 84 40 96 145 273), lower := (rows 7 131 292 74 84 40 96 128 256), losses := [] }

theorem u1663 : Upper (D 6) (R 6) [6,129,288,66,68,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1663
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1664 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 74 84 48 65 168 296), lower := (rows 7 131 292 74 84 48 65 128 256), losses := [] }

theorem u1664 : Upper (D 6) (R 6) [6,129,288,66,68,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1664
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1665 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 7 131 292 74 84 48 72 161 289), lower := (rows 7 131 292 74 84 48 72 128 256), losses := [] }

theorem u1665 : Upper (D 6) (R 6) [6,129,288,66,68,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1665
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1666 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 292 74 84 48 96 137 265), lower := (rows 7 131 292 74 84 48 96 128 256), losses := [] }

theorem u1666 : Upper (D 6) (R 6) [6,129,288,66,68,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1666
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1667 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 268, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 292 76 112 33 66 152 280), lower := (rows 7 131 292 76 112 33 66 128 256), losses := [] }

theorem u1667 : Upper (D 6) (R 6) [6,129,288,68,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1667
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1668 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 131 292 76 112 33 72 146 274), lower := (rows 7 131 292 76 112 33 72 128 256), losses := [] }

theorem u1668 : Upper (D 6) (R 6) [6,129,288,68,96,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1668
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1669 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 131 292 76 112 33 80 138 266), lower := (rows 7 131 292 76 112 33 80 128 256), losses := [] }

theorem u1669 : Upper (D 6) (R 6) [6,129,288,68,96,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1669
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1670 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 268, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 131 292 76 112 34 65 152 280), lower := (rows 7 131 292 76 112 34 65 128 256), losses := [] }

theorem u1670 : Upper (D 6) (R 6) [6,129,288,68,96,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1670
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1671 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 131 292 76 112 34 72 145 273), lower := (rows 7 131 292 76 112 34 72 128 256), losses := [] }

theorem u1671 : Upper (D 6) (R 6) [6,129,288,68,96,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1671
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1672 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 131 292 76 112 34 80 137 265), lower := (rows 7 131 292 76 112 34 80 128 256), losses := [] }

theorem u1672 : Upper (D 6) (R 6) [6,129,288,68,96,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1672
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1673 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 4, region := 292, targets := 1 }], pairs := [(2,0),(3,2),(4,2)], upper := (rows 7 138 276 41 82 96 65 164 292), lower := (rows 7 138 276 41 82 96 65 128 256), losses := [] }

theorem u1673 : Upper (D 6) (R 6) [6,136,272,33,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1673
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1674 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 130, targets := 68 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,2),(1,6),(4,0)], upper := (rows 7 138 276 41 82 96 68 161 289), lower := (rows 7 138 276 41 82 96 68 128 256), losses := [] }

theorem u1674 : Upper (D 6) (R 6) [6,136,272,33,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1674
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1675 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 261, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 138 276 41 82 96 96 133 261), lower := (rows 7 138 276 41 82 96 96 128 256), losses := [] }

theorem u1675 : Upper (D 6) (R 6) [6,136,272,33,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1675
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1676 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 5, region := 260, targets := 1 }], pairs := [(2,0),(3,2),(4,2)], upper := (rows 7 138 292 25 50 96 65 196 324), lower := (rows 7 138 292 25 50 96 65 128 256), losses := [] }

theorem u1676 : Upper (D 6) (R 6) [6,136,288,17,34,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1676
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1677 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 0, region := 112, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 138 292 25 50 96 68 193 321), lower := (rows 7 138 292 25 50 96 68 128 256), losses := [] }

theorem u1677 : Upper (D 6) (R 6) [6,136,288,17,34,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1677
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1678 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 25 82 96 65 164 292), lower := (rows 7 138 292 25 82 96 65 128 256), losses := [] }

theorem u1678 : Upper (D 6) (R 6) [6,136,288,17,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1678
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1679 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 138 292 25 82 96 68 161 289), lower := (rows 7 138 292 25 82 96 68 128 256), losses := [] }

theorem u1679 : Upper (D 6) (R 6) [6,136,288,17,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1679
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1679
end Delivery.IrregularNine14.P06
