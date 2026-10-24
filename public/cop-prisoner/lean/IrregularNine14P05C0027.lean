import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1620 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 296 21 36 72 146 274), lower := (rows 35 67 140 296 21 36 72 128 256), losses := [] }

theorem u1620 : Upper (D 5) (R 5) [34,65,136,288,5,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1620
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1621 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 115, targets := 8 }], pairs := [(0,3)], upper := (rows 35 67 140 296 21 36 80 138 266), lower := (rows 35 67 140 296 21 36 80 128 256), losses := [] }

theorem u1621 : Upper (D 5) (R 5) [34,65,136,288,5,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1621
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1622 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 140 296 22 36 65 152 280), lower := (rows 35 67 140 296 22 36 65 128 256), losses := [] }

theorem u1622 : Upper (D 5) (R 5) [34,65,136,288,6,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1622
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1623 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 296 22 36 72 145 273), lower := (rows 35 67 140 296 22 36 72 128 256), losses := [] }

theorem u1623 : Upper (D 5) (R 5) [34,65,136,288,6,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1623
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1624 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 115, targets := 8 }], pairs := [(0,3)], upper := (rows 35 67 140 296 22 36 80 137 265), lower := (rows 35 67 140 296 22 36 80 128 256), losses := [] }

theorem u1624 : Upper (D 5) (R 5) [34,65,136,288,6,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1624
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1625 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 140 296 26 36 65 148 276), lower := (rows 35 67 140 296 26 36 65 128 256), losses := [] }

theorem u1625 : Upper (D 5) (R 5) [34,65,136,288,10,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1625
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1626 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 67 140 296 26 36 68 145 273), lower := (rows 35 67 140 296 26 36 68 128 256), losses := [] }

theorem u1626 : Upper (D 5) (R 5) [34,65,136,288,10,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1626
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1627 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 140 296 26 36 80 133 261), lower := (rows 35 67 140 296 26 36 80 128 256), losses := [] }

theorem u1627 : Upper (D 5) (R 5) [34,65,136,288,10,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1627
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1628 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 148 296 26 36 65 140 268), lower := (rows 35 67 148 296 26 36 65 128 256), losses := [] }

theorem u1628 : Upper (D 5) (R 5) [34,65,144,288,10,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1628
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1629 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 67 148 296 26 36 68 137 265), lower := (rows 35 67 148 296 26 36 68 128 256), losses := [] }

theorem u1629 : Upper (D 5) (R 5) [34,65,144,288,10,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1629
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1630 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 148 296 26 36 72 133 261), lower := (rows 35 67 148 296 26 36 72 128 256), losses := [] }

theorem u1630 : Upper (D 5) (R 5) [34,65,144,288,10,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1630
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1631 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 44 137 26 288 65 148 276), lower := (rows 35 70 44 137 26 288 65 128 256), losses := [] }

theorem u1631 : Upper (D 5) (R 5) [34,68,40,129,10,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1631
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1632 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 44 137 26 288 68 145 273), lower := (rows 35 70 44 137 26 288 68 128 256), losses := [] }

theorem u1632 : Upper (D 5) (R 5) [34,68,40,129,10,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1632
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1633 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 70 44 137 26 288 80 133 261), lower := (rows 35 70 44 137 26 288 80 128 256), losses := [] }

theorem u1633 : Upper (D 5) (R 5) [34,68,40,129,10,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1633
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1634 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 140, targets := 1 }], pairs := [(2,0)], upper := (rows 35 70 44 138 273 48 65 140 268), lower := (rows 35 70 44 138 273 48 65 128 256), losses := [] }

theorem u1634 : Upper (D 5) (R 5) [34,68,40,130,257,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1634
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1635 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 44 138 273 48 68 137 265), lower := (rows 35 70 44 138 273 48 68 128 256), losses := [] }

theorem u1635 : Upper (D 5) (R 5) [34,68,40,130,257,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1635
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1636 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 305, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 44 138 273 48 72 133 261), lower := (rows 35 70 44 138 273 48 72 128 256), losses := [] }

theorem u1636 : Upper (D 5) (R 5) [34,68,40,130,257,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1636
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1637 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 52 137 26 288 65 140 268), lower := (rows 35 70 52 137 26 288 65 128 256), losses := [] }

theorem u1637 : Upper (D 5) (R 5) [34,68,48,129,10,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1637
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1638 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 425, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 52 137 26 288 68 137 265), lower := (rows 35 70 52 137 26 288 68 128 256), losses := [] }

theorem u1638 : Upper (D 5) (R 5) [34,68,48,129,10,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1638
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1639 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 293, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 52 137 26 288 72 133 261), lower := (rows 35 70 52 137 26 288 72 128 256), losses := [] }

theorem u1639 : Upper (D 5) (R 5) [34,68,48,129,10,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1639
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1640 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 52 137 273 40 66 140 268), lower := (rows 35 70 52 137 273 40 66 128 256), losses := [] }

theorem u1640 : Upper (D 5) (R 5) [34,68,48,129,257,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1640
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1641 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 169, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 52 137 273 40 68 138 266), lower := (rows 35 70 52 137 273 40 68 128 256), losses := [] }

theorem u1641 : Upper (D 5) (R 5) [34,68,48,129,257,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1641
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1642 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 276, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 35 70 52 137 273 40 72 134 262), lower := (rows 35 70 52 137 273 40 72 128 256), losses := [] }

theorem u1642 : Upper (D 5) (R 5) [34,68,48,129,257,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1642
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1643 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 137 274 40 65 140 268), lower := (rows 35 70 52 137 274 40 65 128 256), losses := [] }

theorem u1643 : Upper (D 5) (R 5) [34,68,48,129,258,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1643
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1644 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 169, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 52 137 274 40 68 137 265), lower := (rows 35 70 52 137 274 40 68 128 256), losses := [] }

theorem u1644 : Upper (D 5) (R 5) [34,68,48,129,258,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1644
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1645 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 35 70 52 137 274 40 72 133 261), lower := (rows 35 70 52 137 274 40 72 128 256), losses := [] }

theorem u1645 : Upper (D 5) (R 5) [34,68,48,129,258,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1645
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1646 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 138 273 40 65 140 268), lower := (rows 35 70 52 138 273 40 65 128 256), losses := [] }

theorem u1646 : Upper (D 5) (R 5) [34,68,48,130,257,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1646
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1647 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 169, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 52 138 273 40 68 137 265), lower := (rows 35 70 52 138 273 40 68 128 256), losses := [] }

theorem u1647 : Upper (D 5) (R 5) [34,68,48,130,257,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1647
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1648 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 70 52 138 273 40 72 133 261), lower := (rows 35 70 52 138 273 40 72 128 256), losses := [] }

theorem u1648 : Upper (D 5) (R 5) [34,68,48,130,257,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1648
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1649 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 52 140 25 288 65 138 266), lower := (rows 35 70 52 140 25 288 65 128 256), losses := [] }

theorem u1649 : Upper (D 5) (R 5) [34,68,48,132,9,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1649
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1650 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 156, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 52 140 25 288 66 137 265), lower := (rows 35 70 52 140 25 288 66 128 256), losses := [] }

theorem u1650 : Upper (D 5) (R 5) [34,68,48,132,9,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1650
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1651 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 52 140 25 288 72 131 259), lower := (rows 35 70 52 140 25 288 72 128 256), losses := [] }

theorem u1651 : Upper (D 5) (R 5) [34,68,48,132,9,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1651
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1652 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 140 273 40 65 138 266), lower := (rows 35 70 52 140 273 40 65 128 256), losses := [] }

theorem u1652 : Upper (D 5) (R 5) [34,68,48,132,257,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1652
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1653 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 52 140 273 40 66 137 265), lower := (rows 35 70 52 140 273 40 66 128 256), losses := [] }

theorem u1653 : Upper (D 5) (R 5) [34,68,48,132,257,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1653
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1654 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 272, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 52 140 273 40 72 131 259), lower := (rows 35 70 52 140 273 40 72 128 256), losses := [] }

theorem u1654 : Upper (D 5) (R 5) [34,68,48,132,257,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1654
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1655 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 140 274 40 65 137 265), lower := (rows 35 70 52 140 274 40 65 128 256), losses := [] }

theorem u1655 : Upper (D 5) (R 5) [34,68,48,132,258,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1655
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1656 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 52 140 274 40 72 129 257), lower := (rows 35 70 52 140 274 40 72 128 256), losses := [] }

theorem u1656 : Upper (D 5) (R 5) [34,68,48,132,258,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1656
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1657 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 312, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 56 28 288 65 138 266), lower := (rows 35 70 133 56 28 288 65 128 256), losses := [] }

theorem u1657 : Upper (D 5) (R 5) [34,68,129,48,12,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1657
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1658 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 156, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 133 56 28 288 66 137 265), lower := (rows 35 70 133 56 28 288 66 128 256), losses := [] }

theorem u1658 : Upper (D 5) (R 5) [34,68,129,48,12,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1658
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1659 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 423, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 133 56 28 288 72 131 259), lower := (rows 35 70 133 56 28 288 72 128 256), losses := [] }

theorem u1659 : Upper (D 5) (R 5) [34,68,129,48,12,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1659
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1660 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 133 265 26 40 68 176 304), lower := (rows 35 70 133 265 26 40 68 128 256), losses := [] }

theorem u1660 : Upper (D 5) (R 5) [34,68,129,257,10,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1660
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1661 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 133 265 26 40 80 164 292), lower := (rows 35 70 133 265 26 40 80 128 256), losses := [] }

theorem u1661 : Upper (D 5) (R 5) [34,68,129,257,10,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1661
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1662 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 70 133 265 26 40 96 148 276), lower := (rows 35 70 133 265 26 40 96 128 256), losses := [] }

theorem u1662 : Upper (D 5) (R 5) [34,68,129,257,10,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1662
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1663 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 265 28 40 66 176 304), lower := (rows 35 70 133 265 28 40 66 128 256), losses := [] }

theorem u1663 : Upper (D 5) (R 5) [34,68,129,257,12,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1663
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1664 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 297, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 133 265 28 40 80 162 290), lower := (rows 35 70 133 265 28 40 80 128 256), losses := [] }

theorem u1664 : Upper (D 5) (R 5) [34,68,129,257,12,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1664
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1665 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 70 133 265 28 40 96 146 274), lower := (rows 35 70 133 265 28 40 96 128 256), losses := [] }

theorem u1665 : Upper (D 5) (R 5) [34,68,129,257,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1665
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1666 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 265 52 40 66 152 280), lower := (rows 35 70 133 265 52 40 66 128 256), losses := [] }

theorem u1666 : Upper (D 5) (R 5) [34,68,129,257,36,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1666
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1667 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 148, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 35 70 133 265 52 40 72 146 274), lower := (rows 35 70 133 265 52 40 72 128 256), losses := [] }

theorem u1667 : Upper (D 5) (R 5) [34,68,129,257,36,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1667
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1668 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 133 265 52 40 80 138 266), lower := (rows 35 70 133 265 52 40 80 128 256), losses := [] }

theorem u1668 : Upper (D 5) (R 5) [34,68,129,257,36,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1668
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1669 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 133 266 28 40 65 176 304), lower := (rows 35 70 133 266 28 40 65 128 256), losses := [] }

theorem u1669 : Upper (D 5) (R 5) [34,68,129,258,12,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1669
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1670 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 133 266 28 40 80 161 289), lower := (rows 35 70 133 266 28 40 80 128 256), losses := [] }

theorem u1670 : Upper (D 5) (R 5) [34,68,129,258,12,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1670
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1671 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 70 133 266 28 40 96 145 273), lower := (rows 35 70 133 266 28 40 96 128 256), losses := [] }

theorem u1671 : Upper (D 5) (R 5) [34,68,129,258,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1671
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1672 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 133 266 52 40 65 152 280), lower := (rows 35 70 133 266 52 40 65 128 256), losses := [] }

theorem u1672 : Upper (D 5) (R 5) [34,68,129,258,36,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1672
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1673 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 148, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 70 133 266 52 40 72 145 273), lower := (rows 35 70 133 266 52 40 72 128 256), losses := [] }

theorem u1673 : Upper (D 5) (R 5) [34,68,129,258,36,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1673
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1674 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 133 266 52 40 80 137 265), lower := (rows 35 70 133 266 52 40 80 128 256), losses := [] }

theorem u1674 : Upper (D 5) (R 5) [34,68,129,258,36,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1674
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1675 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 268 25 40 66 176 304), lower := (rows 35 70 133 268 25 40 66 128 256), losses := [] }

theorem u1675 : Upper (D 5) (R 5) [34,68,129,260,9,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1675
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1676 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 132, targets := 8 }], pairs := [(2,3)], upper := (rows 35 70 133 268 25 40 80 162 290), lower := (rows 35 70 133 268 25 40 80 128 256), losses := [] }

theorem u1676 : Upper (D 5) (R 5) [34,68,129,260,9,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1676
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1677 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 70 133 268 25 40 96 146 274), lower := (rows 35 70 133 268 25 40 96 128 256), losses := [] }

theorem u1677 : Upper (D 5) (R 5) [34,68,129,260,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1677
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1678 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 133 268 25 48 66 168 296), lower := (rows 35 70 133 268 25 48 66 128 256), losses := [] }

theorem u1678 : Upper (D 5) (R 5) [34,68,129,260,9,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1678
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1679 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 133 268 25 48 72 162 290), lower := (rows 35 70 133 268 25 48 72 128 256), losses := [] }

theorem u1679 : Upper (D 5) (R 5) [34,68,129,260,9,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1679
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1679
end Delivery.IrregularNine14.P05
