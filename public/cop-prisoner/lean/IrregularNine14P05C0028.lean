import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1680 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 133 268 25 48 96 138 266), lower := (rows 35 70 133 268 25 48 96 128 256), losses := [] }

theorem u1680 : Upper (D 5) (R 5) [34,68,129,260,9,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1680
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1681 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 133 268 26 40 65 176 304), lower := (rows 35 70 133 268 26 40 65 128 256), losses := [] }

theorem u1681 : Upper (D 5) (R 5) [34,68,129,260,10,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1681
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1682 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 133 268 26 40 80 161 289), lower := (rows 35 70 133 268 26 40 80 128 256), losses := [] }

theorem u1682 : Upper (D 5) (R 5) [34,68,129,260,10,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1682
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1683 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 70 133 268 26 40 96 145 273), lower := (rows 35 70 133 268 26 40 96 128 256), losses := [] }

theorem u1683 : Upper (D 5) (R 5) [34,68,129,260,10,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1683
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1684 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 133 280 52 40 65 138 266), lower := (rows 35 70 133 280 52 40 65 128 256), losses := [] }

theorem u1684 : Upper (D 5) (R 5) [34,68,129,272,36,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1684
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1685 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 280 52 40 66 137 265), lower := (rows 35 70 133 280 52 40 66 128 256), losses := [] }

theorem u1685 : Upper (D 5) (R 5) [34,68,129,272,36,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1685
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1686 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 148, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 35 70 133 280 52 40 72 131 259), lower := (rows 35 70 133 280 52 40 72 128 256), losses := [] }

theorem u1686 : Upper (D 5) (R 5) [34,68,129,272,36,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1686
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1687 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 140, targets := 1 }], pairs := [(2,0)], upper := (rows 35 70 134 44 273 48 65 136 264), lower := (rows 35 70 134 44 273 48 65 128 256), losses := [] }

theorem u1687 : Upper (D 5) (R 5) [34,68,130,36,257,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1687
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1688 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 134 44 273 48 72 137 265), lower := (rows 35 70 134 44 273 48 72 128 256), losses := [] }

theorem u1688 : Upper (D 5) (R 5) [34,68,130,36,257,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1688
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1689 : PairBound 9 := { available := 9, camps := [], pairs := [(3,1)], upper := (rows 35 70 134 56 28 288 65 137 265), lower := (rows 35 70 134 56 28 288 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 15 22 355 65 193 321), good := (rows 505 508 188 56 28 288 489 128 288) }] }

theorem u1689 : Upper (D 5) (R 5) [34,68,130,48,12,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1689
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1690 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 423, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 134 56 28 288 72 129 257), lower := (rows 35 70 134 56 28 288 72 128 256), losses := [] }

theorem u1690 : Upper (D 5) (R 5) [34,68,130,48,12,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1690
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1691 : PairBound 9 := { available := 48, camps := [], pairs := [(1,0),(2,0)], upper := (rows 35 70 134 265 28 40 65 176 304), lower := (rows 35 70 134 265 28 40 65 128 256), losses := [{ target := 0, region := (rows 0 66 5 8 24 56 64 184 312), good := (rows 422 70 134 444 444 440 70 128 256) }] }

theorem u1691 : Upper (D 5) (R 5) [34,68,130,257,12,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1691
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1692 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 264, targets := 2 }], pairs := [(3,1)], upper := (rows 35 70 134 265 28 40 80 161 289), lower := (rows 35 70 134 265 28 40 80 128 256), losses := [] }

theorem u1692 : Upper (D 5) (R 5) [34,68,130,257,12,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1692
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1693 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 70 134 265 28 40 96 145 273), lower := (rows 35 70 134 265 28 40 96 128 256), losses := [] }

theorem u1693 : Upper (D 5) (R 5) [34,68,130,257,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1693
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1694 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 134 265 52 40 65 152 280), lower := (rows 35 70 134 265 52 40 65 128 256), losses := [] }

theorem u1694 : Upper (D 5) (R 5) [34,68,130,257,36,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1694
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1695 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 148, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 35 70 134 265 52 40 72 145 273), lower := (rows 35 70 134 265 52 40 72 128 256), losses := [] }

theorem u1695 : Upper (D 5) (R 5) [34,68,130,257,36,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1695
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1696 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 2 }], pairs := [(3,1)], upper := (rows 35 70 134 265 52 40 80 137 265), lower := (rows 35 70 134 265 52 40 80 128 256), losses := [] }

theorem u1696 : Upper (D 5) (R 5) [34,68,130,257,36,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1696
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1697 : PairBound 9 := { available := 48, camps := [], pairs := [(3,1),(4,1)], upper := (rows 35 70 134 268 25 40 65 176 304), lower := (rows 35 70 134 268 25 40 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 17 63 81 209 337), good := (rows 505 492 172 300 505 40 497 128 256) }] }

theorem u1697 : Upper (D 5) (R 5) [34,68,130,260,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1697
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1698 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 132, targets := 8 }], pairs := [(2,3)], upper := (rows 35 70 134 268 25 40 80 161 289), lower := (rows 35 70 134 268 25 40 80 128 256), losses := [] }

theorem u1698 : Upper (D 5) (R 5) [34,68,130,260,9,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1698
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1699 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 70 134 268 25 40 96 145 273), lower := (rows 35 70 134 268 25 40 96 128 256), losses := [] }

theorem u1699 : Upper (D 5) (R 5) [34,68,130,260,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1699
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1700 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0)], upper := (rows 35 70 134 268 25 48 65 168 296), lower := (rows 35 70 134 268 25 48 65 128 256), losses := [] }

theorem u1700 : Upper (D 5) (R 5) [34,68,130,260,9,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1700
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1701 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 134 268 25 48 72 161 289), lower := (rows 35 70 134 268 25 48 72 128 256), losses := [] }

theorem u1701 : Upper (D 5) (R 5) [34,68,130,260,9,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1701
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1702 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 134 268 25 48 96 137 265), lower := (rows 35 70 134 268 25 48 96 128 256), losses := [] }

theorem u1702 : Upper (D 5) (R 5) [34,68,130,260,9,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1702
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1703 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 134 280 52 40 65 137 265), lower := (rows 35 70 134 280 52 40 65 128 256), losses := [] }

theorem u1703 : Upper (D 5) (R 5) [34,68,130,272,36,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1703
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1704 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 148, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 35 70 134 280 52 40 72 129 257), lower := (rows 35 70 134 280 52 40 72 128 256), losses := [] }

theorem u1704 : Upper (D 5) (R 5) [34,68,130,272,36,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1704
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1705 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 66, targets := 8 }], pairs := [(1,3)], upper := (rows 35 70 140 56 21 288 65 138 266), lower := (rows 35 70 140 56 21 288 65 128 256), losses := [] }

theorem u1705 : Upper (D 5) (R 5) [34,68,136,48,5,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1705
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1706 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 156, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 140 56 21 288 66 137 265), lower := (rows 35 70 140 56 21 288 66 128 256), losses := [] }

theorem u1706 : Upper (D 5) (R 5) [34,68,136,48,5,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1706
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1707 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 289, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 140 56 21 288 72 131 259), lower := (rows 35 70 140 56 21 288 72 128 256), losses := [] }

theorem u1707 : Upper (D 5) (R 5) [34,68,136,48,5,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1707
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1708 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 66, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 35 70 140 266 21 40 65 176 304), lower := (rows 35 70 140 266 21 40 65 128 256), losses := [] }

theorem u1708 : Upper (D 5) (R 5) [34,68,136,258,5,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1708
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1709 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 140 266 21 40 80 161 289), lower := (rows 35 70 140 266 21 40 80 128 256), losses := [] }

theorem u1709 : Upper (D 5) (R 5) [34,68,136,258,5,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1709
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1710 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 70 140 266 21 40 96 145 273), lower := (rows 35 70 140 266 21 40 96 128 256), losses := [] }

theorem u1710 : Upper (D 5) (R 5) [34,68,136,258,5,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1710
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1711 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0)], upper := (rows 35 70 140 268 25 48 65 162 290), lower := (rows 35 70 140 268 25 48 65 128 256), losses := [] }

theorem u1711 : Upper (D 5) (R 5) [34,68,136,260,9,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1711
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1712 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 140 268 25 48 66 161 289), lower := (rows 35 70 140 268 25 48 66 128 256), losses := [] }

theorem u1712 : Upper (D 5) (R 5) [34,68,136,260,9,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1712
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1713 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 140 268 25 48 96 131 259), lower := (rows 35 70 140 268 25 48 96 128 256), losses := [] }

theorem u1713 : Upper (D 5) (R 5) [34,68,136,260,9,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1713
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1714 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 70 148 265 26 40 65 164 292), lower := (rows 35 70 148 265 26 40 65 128 256), losses := [] }

theorem u1714 : Upper (D 5) (R 5) [34,68,144,257,10,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1714
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1715 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 297, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 148 265 26 40 68 161 289), lower := (rows 35 70 148 265 26 40 68 128 256), losses := [] }

theorem u1715 : Upper (D 5) (R 5) [34,68,144,257,10,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1715
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1716 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 70 148 265 26 40 96 133 261), lower := (rows 35 70 148 265 26 40 96 128 256), losses := [] }

theorem u1716 : Upper (D 5) (R 5) [34,68,144,257,10,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1716
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1717 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(3,1)], upper := (rows 35 70 148 268 26 40 65 161 289), lower := (rows 35 70 148 268 26 40 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 16 59 65 193 321), good := (rows 489 492 180 300 56 40 481 128 256) }] }

theorem u1717 : Upper (D 5) (R 5) [34,68,144,260,10,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1717
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1718 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 70 148 268 26 40 96 129 257), lower := (rows 35 70 148 268 26 40 96 128 256), losses := [] }

theorem u1718 : Upper (D 5) (R 5) [34,68,144,260,10,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1718
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1719 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 164 265 26 40 65 148 276), lower := (rows 35 70 164 265 26 40 65 128 256), losses := [] }

theorem u1719 : Upper (D 5) (R 5) [34,68,160,257,10,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1719
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1720 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 164 265 26 40 68 145 273), lower := (rows 35 70 164 265 26 40 68 128 256), losses := [] }

theorem u1720 : Upper (D 5) (R 5) [34,68,160,257,10,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1720
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1721 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 164 265 26 40 80 133 261), lower := (rows 35 70 164 265 26 40 80 128 256), losses := [] }

theorem u1721 : Upper (D 5) (R 5) [34,68,160,257,10,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1721
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1722 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 164 265 28 40 65 146 274), lower := (rows 35 70 164 265 28 40 65 128 256), losses := [] }

theorem u1722 : Upper (D 5) (R 5) [34,68,160,257,12,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1722
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1723 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 164 265 28 40 66 145 273), lower := (rows 35 70 164 265 28 40 66 128 256), losses := [] }

theorem u1723 : Upper (D 5) (R 5) [34,68,160,257,12,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1723
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1724 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 297, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 164 265 28 40 80 131 259), lower := (rows 35 70 164 265 28 40 80 128 256), losses := [] }

theorem u1724 : Upper (D 5) (R 5) [34,68,160,257,12,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1724
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1725 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 164 266 28 40 65 145 273), lower := (rows 35 70 164 266 28 40 65 128 256), losses := [] }

theorem u1725 : Upper (D 5) (R 5) [34,68,160,258,12,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1725
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1726 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 164 266 28 40 80 129 257), lower := (rows 35 70 164 266 28 40 80 128 256), losses := [] }

theorem u1726 : Upper (D 5) (R 5) [34,68,160,258,12,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1726
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1727 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 164 268 25 40 65 146 274), lower := (rows 35 70 164 268 25 40 65 128 256), losses := [] }

theorem u1727 : Upper (D 5) (R 5) [34,68,160,260,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1727
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1728 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 164 268 25 40 66 145 273), lower := (rows 35 70 164 268 25 40 66 128 256), losses := [] }

theorem u1728 : Upper (D 5) (R 5) [34,68,160,260,9,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1728
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1729 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 132, targets := 8 }], pairs := [(2,3)], upper := (rows 35 70 164 268 25 40 80 131 259), lower := (rows 35 70 164 268 25 40 80 128 256), losses := [] }

theorem u1729 : Upper (D 5) (R 5) [34,68,160,260,9,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1729
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1730 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 396, targets := 1 }], pairs := [(2,0)], upper := (rows 35 70 164 268 25 48 65 138 266), lower := (rows 35 70 164 268 25 48 65 128 256), losses := [] }

theorem u1730 : Upper (D 5) (R 5) [34,68,160,260,9,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1730
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1731 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 164 268 25 48 66 137 265), lower := (rows 35 70 164 268 25 48 66 128 256), losses := [] }

theorem u1731 : Upper (D 5) (R 5) [34,68,160,260,9,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1731
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1732 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 164 268 25 48 72 131 259), lower := (rows 35 70 164 268 25 48 72 128 256), losses := [] }

theorem u1732 : Upper (D 5) (R 5) [34,68,160,260,9,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1732
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1733 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 164 268 26 40 65 145 273), lower := (rows 35 70 164 268 26 40 65 128 256), losses := [] }

theorem u1733 : Upper (D 5) (R 5) [34,68,160,260,10,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1733
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1734 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 164 268 26 40 80 129 257), lower := (rows 35 70 164 268 26 40 80 128 256), losses := [] }

theorem u1734 : Upper (D 5) (R 5) [34,68,160,260,10,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1734
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1735 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 82 133 266 25 36 68 168 296), lower := (rows 35 82 133 266 25 36 68 128 256), losses := [] }

theorem u1735 : Upper (D 5) (R 5) [34,80,129,258,9,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1735
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1736 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 82 133 266 25 36 72 164 292), lower := (rows 35 82 133 266 25 36 72 128 256), losses := [] }

theorem u1736 : Upper (D 5) (R 5) [34,80,129,258,9,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1736
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1737 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 133 266 25 36 96 140 268), lower := (rows 35 82 133 266 25 36 96 128 256), losses := [] }

theorem u1737 : Upper (D 5) (R 5) [34,80,129,258,9,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1737
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1738 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 82 133 268 25 36 66 168 296), lower := (rows 35 82 133 268 25 36 66 128 256), losses := [] }

theorem u1738 : Upper (D 5) (R 5) [34,80,129,260,9,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1738
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1739 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 82 133 268 25 36 72 162 290), lower := (rows 35 82 133 268 25 36 72 128 256), losses := [] }

theorem u1739 : Upper (D 5) (R 5) [34,80,129,260,9,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1739
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1739
end Delivery.IrregularNine14.P05
