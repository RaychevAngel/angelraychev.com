import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1680 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(3,2),(4,2)], upper := (rows 7 138 292 25 82 96 96 133 261), lower := (rows 7 138 292 25 82 96 96 128 256), losses := [] }

theorem u1680 : Upper (D 6) (R 6) [6,136,288,17,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1680
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1681 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 80, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 138 292 25 84 33 66 224 352), lower := (rows 7 138 292 25 84 33 66 128 256), losses := [] }

theorem u1681 : Upper (D 6) (R 6) [6,136,288,17,68,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1681
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1682 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 138 292 25 84 33 96 194 322), lower := (rows 7 138 292 25 84 33 96 128 256), losses := [] }

theorem u1682 : Upper (D 6) (R 6) [6,136,288,17,68,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1682
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1683 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 88, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 138 292 25 84 34 65 224 352), lower := (rows 7 138 292 25 84 34 65 128 256), losses := [] }

theorem u1683 : Upper (D 6) (R 6) [6,136,288,17,68,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1683
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1684 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 138 292 25 84 34 96 193 321), lower := (rows 7 138 292 25 84 34 96 128 256), losses := [] }

theorem u1684 : Upper (D 6) (R 6) [6,136,288,17,68,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1684
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1685 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 88, targets := 2 },{ cop := 0, region := 88, targets := 32 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 138 292 25 84 96 65 162 290), lower := (rows 7 138 292 25 84 96 65 128 256), losses := [] }

theorem u1685 : Upper (D 6) (R 6) [6,136,288,17,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1685
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1686 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 80, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 138 292 25 84 96 66 161 289), lower := (rows 7 138 292 25 84 96 66 128 256), losses := [] }

theorem u1686 : Upper (D 6) (R 6) [6,136,288,17,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1686
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1687 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 138 292 25 84 96 96 131 259), lower := (rows 7 138 292 25 84 96 96 128 256), losses := [] }

theorem u1687 : Upper (D 6) (R 6) [6,136,288,17,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1687
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1688 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 4, region := 260, targets := 1 }], pairs := [(2,0),(3,2),(4,2)], upper := (rows 7 138 292 25 112 34 65 196 324), lower := (rows 7 138 292 25 112 34 65 128 256), losses := [] }

theorem u1688 : Upper (D 6) (R 6) [6,136,288,17,96,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1688
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1689 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 7 138 292 25 112 34 68 193 321), lower := (rows 7 138 292 25 112 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 20 32 69 137 265), good := (rows 477 392 372 473 112 32 84 128 256) }] }

theorem u1689 : Upper (D 6) (R 6) [6,136,288,17,96,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1689
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1690 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 138 292 26 81 96 65 164 292), lower := (rows 7 138 292 26 81 96 65 128 256), losses := [] }

theorem u1690 : Upper (D 6) (R 6) [6,136,288,18,65,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1690
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1691 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 88, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 138 292 26 81 96 68 161 289), lower := (rows 7 138 292 26 81 96 68 128 256), losses := [] }

theorem u1691 : Upper (D 6) (R 6) [6,136,288,18,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1691
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1692 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 120, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 138 292 26 81 96 96 133 261), lower := (rows 7 138 292 26 81 96 96 128 256), losses := [] }

theorem u1692 : Upper (D 6) (R 6) [6,136,288,18,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1692
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1693 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 88, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 138 292 26 84 33 65 224 352), lower := (rows 7 138 292 26 84 33 65 128 256), losses := [] }

theorem u1693 : Upper (D 6) (R 6) [6,136,288,18,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1693
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1694 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 138 292 26 84 33 96 193 321), lower := (rows 7 138 292 26 84 33 96 128 256), losses := [] }

theorem u1694 : Upper (D 6) (R 6) [6,136,288,18,68,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1694
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1695 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 88, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 138 292 26 84 96 65 161 289), lower := (rows 7 138 292 26 84 96 65 128 256), losses := [] }

theorem u1695 : Upper (D 6) (R 6) [6,136,288,18,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1695
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1696 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 138 292 26 84 96 96 129 257), lower := (rows 7 138 292 26 84 96 96 128 256), losses := [] }

theorem u1696 : Upper (D 6) (R 6) [6,136,288,18,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1696
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1697 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 138 292 26 112 33 65 196 324), lower := (rows 7 138 292 26 112 33 65 128 256), losses := [] }

theorem u1697 : Upper (D 6) (R 6) [6,136,288,18,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1697
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1698 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 2, region := 80, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 7 138 292 26 112 33 68 193 321), lower := (rows 7 138 292 26 112 33 68 128 256), losses := [] }

theorem u1698 : Upper (D 6) (R 6) [6,136,288,18,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1698
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1699 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 138 292 28 81 33 66 224 352), lower := (rows 7 138 292 28 81 33 66 128 256), losses := [] }

theorem u1699 : Upper (D 6) (R 6) [6,136,288,20,65,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1699
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1700 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 7 138 292 28 81 33 96 194 322), lower := (rows 7 138 292 28 81 33 96 128 256), losses := [] }

theorem u1700 : Upper (D 6) (R 6) [6,136,288,20,65,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1700
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1701 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 88, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 138 292 28 81 34 65 224 352), lower := (rows 7 138 292 28 81 34 65 128 256), losses := [] }

theorem u1701 : Upper (D 6) (R 6) [6,136,288,20,65,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1701
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1702 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 7 138 292 28 81 34 96 193 321), lower := (rows 7 138 292 28 81 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 32 100 145 273), good := (rows 477 136 356 476 473 96 96 128 256) }] }

theorem u1702 : Upper (D 6) (R 6) [6,136,288,20,65,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1702
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1703 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 138 292 28 81 96 65 162 290), lower := (rows 7 138 292 28 81 96 65 128 256), losses := [] }

theorem u1703 : Upper (D 6) (R 6) [6,136,288,20,65,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1703
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1704 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 138 292 28 81 96 66 161 289), lower := (rows 7 138 292 28 81 96 66 128 256), losses := [] }

theorem u1704 : Upper (D 6) (R 6) [6,136,288,20,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1704
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1705 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 138 292 28 81 96 96 131 259), lower := (rows 7 138 292 28 81 96 96 128 256), losses := [] }

theorem u1705 : Upper (D 6) (R 6) [6,136,288,20,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1705
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1706 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 138 292 28 82 33 65 224 352), lower := (rows 7 138 292 28 82 33 65 128 256), losses := [] }

theorem u1706 : Upper (D 6) (R 6) [6,136,288,20,66,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1706
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1707 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(2,1),(3,0),(4,2)], upper := (rows 7 138 292 28 82 33 96 193 321), lower := (rows 7 138 292 28 82 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 17 32 100 128 256), good := (rows 94 138 356 92 82 120 96 128 256) }] }

theorem u1707 : Upper (D 6) (R 6) [6,136,288,20,66,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1707
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1708 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 138 292 28 82 96 65 161 289), lower := (rows 7 138 292 28 82 96 65 128 256), losses := [] }

theorem u1708 : Upper (D 6) (R 6) [6,136,288,20,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1708
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1709 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 138 292 28 82 96 96 129 257), lower := (rows 7 138 292 28 82 96 96 128 256), losses := [] }

theorem u1709 : Upper (D 6) (R 6) [6,136,288,20,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1709
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1710 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 4, region := 292, targets := 1 }], pairs := [(2,0),(3,2),(4,2)], upper := (rows 7 138 292 41 82 96 65 148 276), lower := (rows 7 138 292 41 82 96 65 128 256), losses := [] }

theorem u1710 : Upper (D 6) (R 6) [6,136,288,33,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1710
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1711 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 0, region := 80, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 138 292 41 82 96 68 145 273), lower := (rows 7 138 292 41 82 96 68 128 256), losses := [] }

theorem u1711 : Upper (D 6) (R 6) [6,136,288,33,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1711
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1712 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 138 292 41 82 96 80 133 261), lower := (rows 7 138 292 41 82 96 80 128 256), losses := [] }

theorem u1712 : Upper (D 6) (R 6) [6,136,288,33,66,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1712
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1713 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 0, region := 104, targets := 4 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 7 138 292 41 84 96 65 146 274), lower := (rows 7 138 292 41 84 96 65 128 256), losses := [] }

theorem u1713 : Upper (D 6) (R 6) [6,136,288,33,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1713
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1714 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 104, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,0),(4,5)], upper := (rows 7 138 292 41 84 96 66 145 273), lower := (rows 7 138 292 41 84 96 66 128 256), losses := [] }

theorem u1714 : Upper (D 6) (R 6) [6,136,288,33,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1714
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1715 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 138 292 41 84 96 80 131 259), lower := (rows 7 138 292 41 84 96 80 128 256), losses := [] }

theorem u1715 : Upper (D 6) (R 6) [6,136,288,33,68,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1715
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1716 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,2),(4,2)], upper := (rows 7 138 292 56 82 33 65 196 324), lower := (rows 7 138 292 56 82 33 65 128 256), losses := [] }

theorem u1716 : Upper (D 6) (R 6) [6,136,288,48,66,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1716
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1717 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 356, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,0),(4,5)], upper := (rows 7 138 292 56 82 33 68 193 321), lower := (rows 7 138 292 56 82 33 68 128 256), losses := [] }

theorem u1717 : Upper (D 6) (R 6) [6,136,288,48,66,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1717
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1718 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 7 138 292 56 84 33 65 194 322), lower := (rows 7 138 292 56 84 33 65 128 256), losses := [] }

theorem u1718 : Upper (D 6) (R 6) [6,136,288,48,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1718
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1719 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,0),(4,0),(4,5)], upper := (rows 7 138 292 56 84 33 66 193 321), lower := (rows 7 138 292 56 84 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 40 17 32 67 128 256), good := (rows 86 202 300 56 84 120 66 128 256) }] }

theorem u1719 : Upper (D 6) (R 6) [6,136,288,48,68,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1719
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1720 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 80, targets := 34 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 138 292 56 84 34 65 193 321), lower := (rows 7 138 292 56 84 34 65 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 59 65 193 321), good := (rows 483 170 288 58 506 34 481 128 256) }] }

theorem u1720 : Upper (D 6) (R 6) [6,136,288,48,68,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1720
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1721 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 73 49 96 66 148 276), lower := (rows 7 138 292 73 49 96 66 128 256), losses := [] }

theorem u1721 : Upper (D 6) (R 6) [6,136,288,65,33,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1721
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1722 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 3, region := 178, targets := 4 }], pairs := [(1,2),(3,1),(4,1)], upper := (rows 7 138 292 73 49 96 68 146 274), lower := (rows 7 138 292 73 49 96 68 128 256), losses := [] }

theorem u1722 : Upper (D 6) (R 6) [6,136,288,65,33,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1722
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1723 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 120, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 138 292 73 49 96 80 134 262), lower := (rows 7 138 292 73 49 96 80 128 256), losses := [] }

theorem u1723 : Upper (D 6) (R 6) [6,136,288,65,33,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1723
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1724 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 3, region := 178, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 138 292 73 82 33 68 176 304), lower := (rows 7 138 292 73 82 33 68 128 256), losses := [] }

theorem u1724 : Upper (D 6) (R 6) [6,136,288,65,66,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1724
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1725 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 138 292 73 82 33 80 164 292), lower := (rows 7 138 292 73 82 33 80 128 256), losses := [] }

theorem u1725 : Upper (D 6) (R 6) [6,136,288,65,66,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1725
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1726 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 4, region := 293, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 138 292 73 82 33 96 148 276), lower := (rows 7 138 292 73 82 33 96 128 256), losses := [] }

theorem u1726 : Upper (D 6) (R 6) [6,136,288,65,66,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1726
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1727 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 3, region := 308, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 138 292 73 84 33 66 176 304), lower := (rows 7 138 292 73 84 33 66 128 256), losses := [] }

theorem u1727 : Upper (D 6) (R 6) [6,136,288,65,68,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1727
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1728 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 138 292 73 84 33 80 162 290), lower := (rows 7 138 292 73 84 33 80 128 256), losses := [] }

theorem u1728 : Upper (D 6) (R 6) [6,136,288,65,68,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1728
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1729 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 138 292 73 84 33 96 146 274), lower := (rows 7 138 292 73 84 33 96 128 256), losses := [] }

theorem u1729 : Upper (D 6) (R 6) [6,136,288,65,68,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1729
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1730 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 88, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 138 292 73 84 34 65 176 304), lower := (rows 7 138 292 73 84 34 65 128 256), losses := [] }

theorem u1730 : Upper (D 6) (R 6) [6,136,288,65,68,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1730
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1731 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 138 292 73 84 34 80 161 289), lower := (rows 7 138 292 73 84 34 80 128 256), losses := [] }

theorem u1731 : Upper (D 6) (R 6) [6,136,288,65,68,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1731
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1732 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 138 292 73 84 34 96 145 273), lower := (rows 7 138 292 73 84 34 96 128 256), losses := [] }

theorem u1732 : Upper (D 6) (R 6) [6,136,288,65,68,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1732
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1733 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 138 292 73 84 48 65 162 290), lower := (rows 7 138 292 73 84 48 65 128 256), losses := [] }

theorem u1733 : Upper (D 6) (R 6) [6,136,288,65,68,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1733
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1734 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 138 292 73 84 48 66 161 289), lower := (rows 7 138 292 73 84 48 66 128 256), losses := [] }

theorem u1734 : Upper (D 6) (R 6) [6,136,288,65,68,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1734
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1735 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 138 292 73 84 48 96 131 259), lower := (rows 7 138 292 73 84 48 96 128 256), losses := [] }

theorem u1735 : Upper (D 6) (R 6) [6,136,288,65,68,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1735
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1736 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 138 292 73 112 33 66 148 276), lower := (rows 7 138 292 73 112 33 66 128 256), losses := [] }

theorem u1736 : Upper (D 6) (R 6) [6,136,288,65,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1736
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1737 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 3, region := 178, targets := 4 }], pairs := [(1,2),(3,1),(4,1)], upper := (rows 7 138 292 73 112 33 68 146 274), lower := (rows 7 138 292 73 112 33 68 128 256), losses := [] }

theorem u1737 : Upper (D 6) (R 6) [6,136,288,65,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1737
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1738 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 120, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 138 292 73 112 33 80 134 262), lower := (rows 7 138 292 73 112 33 80 128 256), losses := [] }

theorem u1738 : Upper (D 6) (R 6) [6,136,288,65,96,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1738
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1739 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 138 292 73 112 34 65 148 276), lower := (rows 7 138 292 73 112 34 65 128 256), losses := [] }

theorem u1739 : Upper (D 6) (R 6) [6,136,288,65,96,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1739
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1739
end Delivery.IrregularNine14.P06
