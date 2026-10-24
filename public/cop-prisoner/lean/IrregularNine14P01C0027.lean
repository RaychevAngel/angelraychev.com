import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1620 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 277 50 44 74 144 34 193 193 449), lower := (rows 277 50 44 74 144 34 64 128 256), losses := [] }

theorem u1620 : Upper (D 1) (R 1) [276,48,40,66,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1620
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1621 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 277 50 44 74 144 96 195 131 387), lower := (rows 277 50 44 74 144 96 64 128 256), losses := [] }

theorem u1621 : Upper (D 1) (R 1) [276,48,40,66,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1621
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1622 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 277 50 44 74 144 160 67 195 323), lower := (rows 277 50 44 74 144 160 64 128 256), losses := [] }

theorem u1622 : Upper (D 1) (R 1) [276,48,40,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1622
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1623 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 70 41 144 34 200 200 456), lower := (rows 277 50 70 41 144 34 64 128 256), losses := [] }

theorem u1623 : Upper (D 1) (R 1) [276,48,66,33,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1623
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1624 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 50 70 41 144 40 194 194 450), lower := (rows 277 50 70 41 144 40 64 128 256), losses := [] }

theorem u1624 : Upper (D 1) (R 1) [276,48,66,33,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1624
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1625 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 146, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 70 41 144 96 202 138 394), lower := (rows 277 50 70 41 144 96 64 128 256), losses := [] }

theorem u1625 : Upper (D 1) (R 1) [276,48,66,33,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1625
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1626 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 277 50 70 41 144 160 74 202 330), lower := (rows 277 50 70 41 144 160 64 128 256), losses := [] }

theorem u1626 : Upper (D 1) (R 1) [276,48,66,33,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1626
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1627 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 277 50 70 104 144 33 202 138 394), lower := (rows 277 50 70 104 144 33 64 128 256), losses := [] }

theorem u1627 : Upper (D 1) (R 1) [276,48,66,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1627
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1628 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 70 104 144 34 201 137 393), lower := (rows 277 50 70 104 144 34 64 128 256), losses := [] }

theorem u1628 : Upper (D 1) (R 1) [276,48,66,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1628
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1629 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 277 50 70 104 144 40 195 131 387), lower := (rows 277 50 70 104 144 40 64 128 256), losses := [] }

theorem u1629 : Upper (D 1) (R 1) [276,48,66,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1629
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1630 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 277 50 70 104 144 160 75 139 267), lower := (rows 277 50 70 104 144 160 64 128 256), losses := [] }

theorem u1630 : Upper (D 1) (R 1) [276,48,66,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1630
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1631 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 70 137 144 34 104 232 360), lower := (rows 277 50 70 137 144 34 64 128 256), losses := [] }

theorem u1631 : Upper (D 1) (R 1) [276,48,66,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1631
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1632 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 277 50 70 137 144 40 98 226 354), lower := (rows 277 50 70 137 144 40 64 128 256), losses := [] }

theorem u1632 : Upper (D 1) (R 1) [276,48,66,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1632
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1633 : PairBound 9 := { available := 42, camps := [], pairs := [(1,7)], upper := (rows 277 50 70 137 144 96 106 170 298), lower := (rows 277 50 70 137 144 96 64 128 256), losses := [{ target := 7, region := (rows 1 3 12 8 16 108 72 0 264), good := (rows 311 50 102 367 16 96 96 0 256) }] }

theorem u1633 : Upper (D 1) (R 1) [276,48,66,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1633
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1634 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 277 50 70 138 144 33 104 232 360), lower := (rows 277 50 70 138 144 33 64 128 256), losses := [] }

theorem u1634 : Upper (D 1) (R 1) [276,48,66,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1634
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1635 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 277 50 70 138 144 40 97 225 353), lower := (rows 277 50 70 138 144 40 64 128 256), losses := [] }

theorem u1635 : Upper (D 1) (R 1) [276,48,66,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1635
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1636 : PairBound 9 := { available := 41, camps := [], pairs := [(1,7)], upper := (rows 277 50 70 138 144 96 105 169 297), lower := (rows 277 50 70 138 144 96 64 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 16 100 64 0 256), good := (rows 311 50 102 10 16 96 96 0 256) }] }

theorem u1636 : Upper (D 1) (R 1) [276,48,66,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1636
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1637 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 277 50 70 200 144 33 106 170 298), lower := (rows 277 50 70 200 144 33 64 128 256), losses := [] }

theorem u1637 : Upper (D 1) (R 1) [276,48,66,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1637
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1638 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 70 200 144 34 105 169 297), lower := (rows 277 50 70 200 144 34 64 128 256), losses := [] }

theorem u1638 : Upper (D 1) (R 1) [276,48,66,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1638
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1639 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 277 50 70 200 144 40 99 163 291), lower := (rows 277 50 70 200 144 40 64 128 256), losses := [] }

theorem u1639 : Upper (D 1) (R 1) [276,48,66,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1639
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1640 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 76 41 144 34 194 194 450), lower := (rows 277 50 76 41 144 34 64 128 256), losses := [] }

theorem u1640 : Upper (D 1) (R 1) [276,48,72,33,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1640
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1641 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 146, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 76 41 144 96 194 130 386), lower := (rows 277 50 76 41 144 96 64 128 256), losses := [] }

theorem u1641 : Upper (D 1) (R 1) [276,48,72,33,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1641
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1642 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 277 50 76 41 144 160 66 194 322), lower := (rows 277 50 76 41 144 160 64 128 256), losses := [] }

theorem u1642 : Upper (D 1) (R 1) [276,48,72,33,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1642
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1643 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 277 50 100 74 144 33 202 138 394), lower := (rows 277 50 100 74 144 33 64 128 256), losses := [] }

theorem u1643 : Upper (D 1) (R 1) [276,48,96,66,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1643
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1644 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 100 74 144 34 201 137 393), lower := (rows 277 50 100 74 144 34 64 128 256), losses := [] }

theorem u1644 : Upper (D 1) (R 1) [276,48,96,66,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1644
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1645 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 277 50 100 74 144 40 195 131 387), lower := (rows 277 50 100 74 144 40 64 128 256), losses := [] }

theorem u1645 : Upper (D 1) (R 1) [276,48,96,66,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1645
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1646 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 277 50 100 74 144 160 75 139 267), lower := (rows 277 50 100 74 144 160 64 128 256), losses := [] }

theorem u1646 : Upper (D 1) (R 1) [276,48,96,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1646
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1647 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 100 137 144 34 74 202 330), lower := (rows 277 50 100 137 144 34 64 128 256), losses := [] }

theorem u1647 : Upper (D 1) (R 1) [276,48,96,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1647
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1648 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 277 50 100 137 144 40 66 194 322), lower := (rows 277 50 100 137 144 40 64 128 256), losses := [] }

theorem u1648 : Upper (D 1) (R 1) [276,48,96,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1648
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1649 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 50 100 137 144 96 74 138 266), lower := (rows 277 50 100 137 144 96 64 128 256), losses := [] }

theorem u1649 : Upper (D 1) (R 1) [276,48,96,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1649
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1650 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 277 50 100 138 144 33 74 202 330), lower := (rows 277 50 100 138 144 33 64 128 256), losses := [] }

theorem u1650 : Upper (D 1) (R 1) [276,48,96,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1650
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1651 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 100 138 144 34 73 201 329), lower := (rows 277 50 100 138 144 34 64 128 256), losses := [] }

theorem u1651 : Upper (D 1) (R 1) [276,48,96,130,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1651
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1652 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 277 50 100 138 144 40 67 195 323), lower := (rows 277 50 100 138 144 40 64 128 256), losses := [] }

theorem u1652 : Upper (D 1) (R 1) [276,48,96,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1652
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1653 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 50 100 138 144 96 75 139 267), lower := (rows 277 50 100 138 144 96 64 128 256), losses := [] }

theorem u1653 : Upper (D 1) (R 1) [276,48,96,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1653
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1654 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 277 50 100 200 144 33 74 138 266), lower := (rows 277 50 100 200 144 33 64 128 256), losses := [] }

theorem u1654 : Upper (D 1) (R 1) [276,48,96,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1654
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1655 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 100 200 144 34 75 139 267), lower := (rows 277 50 100 200 144 34 64 128 256), losses := [] }

theorem u1655 : Upper (D 1) (R 1) [276,48,96,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1655
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1656 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 277 50 100 200 144 40 67 131 259), lower := (rows 277 50 100 200 144 40 64 128 256), losses := [] }

theorem u1656 : Upper (D 1) (R 1) [276,48,96,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1656
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1657 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 277 98 7 138 144 40 112 240 368), lower := (rows 277 98 7 138 144 40 64 128 256), losses := [] }

theorem u1657 : Upper (D 1) (R 1) [276,96,3,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1657
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1658 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 7 138 144 48 104 232 360), lower := (rows 277 98 7 138 144 48 64 128 256), losses := [] }

theorem u1658 : Upper (D 1) (R 1) [276,96,3,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1658
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1659 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 7 138 144 96 120 184 312), lower := (rows 277 98 7 138 144 96 64 128 256), losses := [] }

theorem u1659 : Upper (D 1) (R 1) [276,96,3,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1659
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1660 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 152, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 7 168 80 34 216 152 408), lower := (rows 277 98 7 168 80 34 64 128 256), losses := [] }

theorem u1660 : Upper (D 1) (R 1) [276,96,3,160,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1660
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1661 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 98 7 168 80 40 210 146 402), lower := (rows 277 98 7 168 80 40 64 128 256), losses := [] }

theorem u1661 : Upper (D 1) (R 1) [276,96,3,160,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1661
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1662 : PairBound 9 := { available := 138, camps := [{ cop := 5, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 7 168 80 48 202 138 394), lower := (rows 277 98 7 168 80 48 64 128 256), losses := [] }

theorem u1662 : Upper (D 1) (R 1) [276,96,3,160,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1662
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1663 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 277 98 7 168 80 160 90 154 282), lower := (rows 277 98 7 168 80 160 64 128 256), losses := [] }

theorem u1663 : Upper (D 1) (R 1) [276,96,3,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1663
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1664 : PairBound 9 := { available := 88, camps := [{ cop := 6, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 7 168 144 34 88 216 344), lower := (rows 277 98 7 168 144 34 64 128 256), losses := [] }

theorem u1664 : Upper (D 1) (R 1) [276,96,3,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1664
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1665 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 277 98 7 168 144 40 82 210 338), lower := (rows 277 98 7 168 144 40 64 128 256), losses := [] }

theorem u1665 : Upper (D 1) (R 1) [276,96,3,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1665
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1666 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 7 168 144 48 74 202 330), lower := (rows 277 98 7 168 144 48 64 128 256), losses := [] }

theorem u1666 : Upper (D 1) (R 1) [276,96,3,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1666
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1667 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 7 168 144 96 90 154 282), lower := (rows 277 98 7 168 144 96 64 128 256), losses := [] }

theorem u1667 : Upper (D 1) (R 1) [276,96,3,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1667
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1668 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 13 138 18 48 224 224 480), lower := (rows 277 98 13 138 18 48 64 128 256), losses := [] }

theorem u1668 : Upper (D 1) (R 1) [276,96,9,130,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1668
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1669 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 13 138 18 96 240 176 432), lower := (rows 277 98 13 138 18 96 64 128 256), losses := [] }

theorem u1669 : Upper (D 1) (R 1) [276,96,9,130,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1669
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1670 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 82, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 13 138 18 160 112 240 368), lower := (rows 277 98 13 138 18 160 64 128 256), losses := [] }

theorem u1670 : Upper (D 1) (R 1) [276,96,9,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1670
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1671 : PairBound 9 := { available := 208, camps := [{ cop := 6, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 13 138 48 34 208 208 464), lower := (rows 277 98 13 138 48 34 64 128 256), losses := [] }

theorem u1671 : Upper (D 1) (R 1) [276,96,9,130,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1671
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1672 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 136, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 13 138 48 48 194 194 450), lower := (rows 277 98 13 138 48 48 64 128 256), losses := [] }

theorem u1672 : Upper (D 1) (R 1) [276,96,9,130,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1672
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1673 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 13 138 48 96 210 146 402), lower := (rows 277 98 13 138 48 96 64 128 256), losses := [] }

theorem u1673 : Upper (D 1) (R 1) [276,96,9,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1673
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1674 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 13 138 48 160 82 210 338), lower := (rows 277 98 13 138 48 160 64 128 256), losses := [] }

theorem u1674 : Upper (D 1) (R 1) [276,96,9,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1674
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1675 : PairBound 9 := { available := 208, camps := [{ cop := 6, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 13 168 18 34 208 208 464), lower := (rows 277 98 13 168 18 34 64 128 256), losses := [] }

theorem u1675 : Upper (D 1) (R 1) [276,96,9,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1675
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1676 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 13 168 18 48 194 194 450), lower := (rows 277 98 13 168 18 48 64 128 256), losses := [] }

theorem u1676 : Upper (D 1) (R 1) [276,96,9,160,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1676
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1677 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 13 168 18 96 210 146 402), lower := (rows 277 98 13 168 18 96 64 128 256), losses := [] }

theorem u1677 : Upper (D 1) (R 1) [276,96,9,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1677
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1678 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 277 98 13 168 18 160 82 210 338), lower := (rows 277 98 13 168 18 160 64 128 256), losses := [] }

theorem u1678 : Upper (D 1) (R 1) [276,96,9,160,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1678
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1679 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 13 168 80 34 210 146 402), lower := (rows 277 98 13 168 80 34 64 128 256), losses := [] }

theorem u1679 : Upper (D 1) (R 1) [276,96,9,160,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1679
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1679
end Delivery.IrregularNine14.P01
