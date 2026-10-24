import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1740 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 72, targets := 34 },{ cop := 2, region := 80, targets := 1 }], pairs := [(3,1),(3,5),(4,0)], upper := (rows 7 138 292 73 112 34 68 145 273), lower := (rows 7 138 292 73 112 34 68 128 256), losses := [] }

theorem u1740 : Upper (D 6) (R 6) [6,136,288,65,96,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1740
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1741 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 138 292 73 112 34 80 133 261), lower := (rows 7 138 292 73 112 34 80 128 256), losses := [] }

theorem u1741 : Upper (D 6) (R 6) [6,136,288,65,96,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1741
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1742 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 72, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 138 292 74 84 33 65 176 304), lower := (rows 7 138 292 74 84 33 65 128 256), losses := [] }

theorem u1742 : Upper (D 6) (R 6) [6,136,288,66,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1742
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1743 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 138 292 74 84 33 80 161 289), lower := (rows 7 138 292 74 84 33 80 128 256), losses := [] }

theorem u1743 : Upper (D 6) (R 6) [6,136,288,66,68,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1743
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1744 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 138 292 74 84 33 96 145 273), lower := (rows 7 138 292 74 84 33 96 128 256), losses := [] }

theorem u1744 : Upper (D 6) (R 6) [6,136,288,66,68,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1744
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1745 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 138 292 74 112 33 65 148 276), lower := (rows 7 138 292 74 112 33 65 128 256), losses := [] }

theorem u1745 : Upper (D 6) (R 6) [6,136,288,66,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1745
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1746 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 72, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 138 292 74 112 33 68 145 273), lower := (rows 7 138 292 74 112 33 68 128 256), losses := [] }

theorem u1746 : Upper (D 6) (R 6) [6,136,288,66,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1746
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1747 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 138 292 74 112 33 80 133 261), lower := (rows 7 138 292 74 112 33 80 128 256), losses := [] }

theorem u1747 : Upper (D 6) (R 6) [6,136,288,66,96,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1747
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1748 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 7 138 292 76 49 96 65 146 274), lower := (rows 7 138 292 76 49 96 65 128 256), losses := [] }

theorem u1748 : Upper (D 6) (R 6) [6,136,288,68,33,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1748
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1749 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 260, targets := 66 },{ cop := 0, region := 72, targets := 1 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 7 138 292 76 49 96 66 145 273), lower := (rows 7 138 292 76 49 96 66 128 256), losses := [] }

theorem u1749 : Upper (D 6) (R 6) [6,136,288,68,33,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1749
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1750 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 7 138 292 76 49 96 80 131 259), lower := (rows 7 138 292 76 49 96 80 128 256), losses := [] }

theorem u1750 : Upper (D 6) (R 6) [6,136,288,68,33,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1750
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1751 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 72, targets := 2 },{ cop := 0, region := 48, targets := 4 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,1),(3,5),(4,2)], upper := (rows 7 138 292 76 50 33 65 208 336), lower := (rows 7 138 292 76 50 33 65 128 256), losses := [] }

theorem u1751 : Upper (D 6) (R 6) [6,136,288,68,34,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1751
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1752 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 138 292 76 50 33 80 193 321), lower := (rows 7 138 292 76 50 33 80 128 256), losses := [] }

theorem u1752 : Upper (D 6) (R 6) [6,136,288,68,34,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1752
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1753 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 138 292 76 81 33 66 176 304), lower := (rows 7 138 292 76 81 33 66 128 256), losses := [] }

theorem u1753 : Upper (D 6) (R 6) [6,136,288,68,65,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1753
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1754 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 138 292 76 81 33 80 162 290), lower := (rows 7 138 292 76 81 33 80 128 256), losses := [] }

theorem u1754 : Upper (D 6) (R 6) [6,136,288,68,65,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1754
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1755 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 138 292 76 81 33 96 146 274), lower := (rows 7 138 292 76 81 33 96 128 256), losses := [] }

theorem u1755 : Upper (D 6) (R 6) [6,136,288,68,65,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1755
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1756 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 88, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 138 292 76 81 34 65 176 304), lower := (rows 7 138 292 76 81 34 65 128 256), losses := [] }

theorem u1756 : Upper (D 6) (R 6) [6,136,288,68,65,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1756
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1757 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 138 292 76 81 34 80 161 289), lower := (rows 7 138 292 76 81 34 80 128 256), losses := [] }

theorem u1757 : Upper (D 6) (R 6) [6,136,288,68,65,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1757
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1758 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 138 292 76 81 34 96 145 273), lower := (rows 7 138 292 76 81 34 96 128 256), losses := [] }

theorem u1758 : Upper (D 6) (R 6) [6,136,288,68,65,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1758
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1759 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 138 292 76 81 48 65 162 290), lower := (rows 7 138 292 76 81 48 65 128 256), losses := [] }

theorem u1759 : Upper (D 6) (R 6) [6,136,288,68,65,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1759
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1760 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 138 292 76 81 48 66 161 289), lower := (rows 7 138 292 76 81 48 66 128 256), losses := [] }

theorem u1760 : Upper (D 6) (R 6) [6,136,288,68,65,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1760
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1761 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 138 292 76 81 48 96 131 259), lower := (rows 7 138 292 76 81 48 96 128 256), losses := [] }

theorem u1761 : Upper (D 6) (R 6) [6,136,288,68,65,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1761
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1762 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 138 292 76 112 33 65 146 274), lower := (rows 7 138 292 76 112 33 65 128 256), losses := [] }

theorem u1762 : Upper (D 6) (R 6) [6,136,288,68,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1762
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1763 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 72, targets := 1 },{ cop := 0, region := 112, targets := 4 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,0),(3,5),(4,2)], upper := (rows 7 138 292 76 112 33 66 145 273), lower := (rows 7 138 292 76 112 33 66 128 256), losses := [] }

theorem u1763 : Upper (D 6) (R 6) [6,136,288,68,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1763
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1764 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 138 292 76 112 33 80 131 259), lower := (rows 7 138 292 76 112 33 80 128 256), losses := [] }

theorem u1764 : Upper (D 6) (R 6) [6,136,288,68,96,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1764
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1765 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 72, targets := 34 },{ cop := 0, region := 112, targets := 4 }], pairs := [(3,1),(3,5),(4,2)], upper := (rows 7 138 292 76 112 34 65 145 273), lower := (rows 7 138 292 76 112 34 65 128 256), losses := [] }

theorem u1765 : Upper (D 6) (R 6) [6,136,288,68,96,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1765
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1766 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 138 292 76 112 34 80 129 257), lower := (rows 7 138 292 76 112 34 80 128 256), losses := [] }

theorem u1766 : Upper (D 6) (R 6) [6,136,288,68,96,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1766
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1767 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 138 292 104 84 33 65 146 274), lower := (rows 7 138 292 104 84 33 65 128 256), losses := [] }

theorem u1767 : Upper (D 6) (R 6) [6,136,288,96,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1767
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1768 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 104, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,0),(4,5)], upper := (rows 7 138 292 104 84 33 66 145 273), lower := (rows 7 138 292 104 84 33 66 128 256), losses := [] }

theorem u1768 : Upper (D 6) (R 6) [6,136,288,96,68,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1768
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1769 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 138 292 104 84 33 80 131 259), lower := (rows 7 138 292 104 84 33 80 128 256), losses := [] }

theorem u1769 : Upper (D 6) (R 6) [6,136,288,96,68,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1769
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1770 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 34 },{ cop := 0, region := 104, targets := 4 }], pairs := [(3,2),(4,1),(4,5)], upper := (rows 7 138 292 104 84 34 65 145 273), lower := (rows 7 138 292 104 84 34 65 128 256), losses := [] }

theorem u1770 : Upper (D 6) (R 6) [6,136,288,96,68,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1770
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1771 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 138 292 104 84 34 80 129 257), lower := (rows 7 138 292 104 84 34 80 128 256), losses := [] }

theorem u1771 : Upper (D 6) (R 6) [6,136,288,96,68,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1771
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1772 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 162 292 26 81 96 65 140 268), lower := (rows 7 162 292 26 81 96 65 128 256), losses := [] }

theorem u1772 : Upper (D 6) (R 6) [6,160,288,18,65,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1772
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1773 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 4, region := 170, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 162 292 26 81 96 68 137 265), lower := (rows 7 162 292 26 81 96 68 128 256), losses := [] }

theorem u1773 : Upper (D 6) (R 6) [6,160,288,18,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1773
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1774 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 162 292 26 81 96 72 133 261), lower := (rows 7 162 292 26 81 96 72 128 256), losses := [] }

theorem u1774 : Upper (D 6) (R 6) [6,160,288,18,65,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1774
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1775 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 162 292 26 84 33 65 200 328), lower := (rows 7 162 292 26 84 33 65 128 256), losses := [] }

theorem u1775 : Upper (D 6) (R 6) [6,160,288,18,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1775
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1776 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 88, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 162 292 26 84 33 72 193 321), lower := (rows 7 162 292 26 84 33 72 128 256), losses := [] }

theorem u1776 : Upper (D 6) (R 6) [6,160,288,18,68,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1776
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1777 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 162 292 26 84 96 65 137 265), lower := (rows 7 162 292 26 84 96 65 128 256), losses := [] }

theorem u1777 : Upper (D 6) (R 6) [6,160,288,18,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1777
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1778 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 162 292 26 84 96 72 129 257), lower := (rows 7 162 292 26 84 96 72 128 256), losses := [] }

theorem u1778 : Upper (D 6) (R 6) [6,160,288,18,68,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1778
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1779 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 3, region := 178, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 162 292 73 82 33 68 152 280), lower := (rows 7 162 292 73 82 33 68 128 256), losses := [] }

theorem u1779 : Upper (D 6) (R 6) [6,160,288,65,66,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1779
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1780 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 162 292 73 82 33 72 148 276), lower := (rows 7 162 292 73 82 33 72 128 256), losses := [] }

theorem u1780 : Upper (D 6) (R 6) [6,160,288,65,66,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1780
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1781 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 162 292 73 82 33 80 140 268), lower := (rows 7 162 292 73 82 33 80 128 256), losses := [] }

theorem u1781 : Upper (D 6) (R 6) [6,160,288,65,66,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1781
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1782 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 162 292 74 84 33 65 152 280), lower := (rows 7 162 292 74 84 33 65 128 256), losses := [] }

theorem u1782 : Upper (D 6) (R 6) [6,160,288,66,68,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1782
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1783 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 162 292 74 84 33 72 145 273), lower := (rows 7 162 292 74 84 33 72 128 256), losses := [] }

theorem u1783 : Upper (D 6) (R 6) [6,160,288,66,68,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1783
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1784 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 1, region := 80, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 7 162 324 25 112 33 66 140 268), lower := (rows 7 162 324 25 112 33 66 128 256), losses := [] }

theorem u1784 : Upper (D 6) (R 6) [6,160,320,17,96,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1784
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1785 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 162 324 25 112 33 68 138 266), lower := (rows 7 162 324 25 112 33 68 128 256), losses := [] }

theorem u1785 : Upper (D 6) (R 6) [6,160,320,17,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1785
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1786 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 120, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 162 324 25 112 33 72 134 262), lower := (rows 7 162 324 25 112 33 72 128 256), losses := [] }

theorem u1786 : Upper (D 6) (R 6) [6,160,320,17,96,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1786
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1787 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 170, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 162 324 26 81 33 68 168 296), lower := (rows 7 162 324 26 81 33 68 128 256), losses := [] }

theorem u1787 : Upper (D 6) (R 6) [6,160,320,18,65,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1787
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1788 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 162 324 26 81 33 72 164 292), lower := (rows 7 162 324 26 81 33 72 128 256), losses := [] }

theorem u1788 : Upper (D 6) (R 6) [6,160,320,18,65,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1788
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1789 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 0, region := 112, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 7 162 324 26 81 33 96 140 268), lower := (rows 7 162 324 26 81 33 96 128 256), losses := [] }

theorem u1789 : Upper (D 6) (R 6) [6,160,320,18,65,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1789
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1790 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 162 324 26 81 36 65 168 296), lower := (rows 7 162 324 26 81 36 65 128 256), losses := [] }

theorem u1790 : Upper (D 6) (R 6) [6,160,320,18,65,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1790
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1791 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 162 324 26 81 36 72 161 289), lower := (rows 7 162 324 26 81 36 72 128 256), losses := [] }

theorem u1791 : Upper (D 6) (R 6) [6,160,320,18,65,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1791
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1792 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 0, region := 112, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 162 324 26 81 36 96 137 265), lower := (rows 7 162 324 26 81 36 96 128 256), losses := [] }

theorem u1792 : Upper (D 6) (R 6) [6,160,320,18,65,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1792
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1793 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 162 324 26 81 40 65 164 292), lower := (rows 7 162 324 26 81 40 65 128 256), losses := [] }

theorem u1793 : Upper (D 6) (R 6) [6,160,320,18,65,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1793
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1794 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 170, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 162 324 26 81 40 68 161 289), lower := (rows 7 162 324 26 81 40 68 128 256), losses := [] }

theorem u1794 : Upper (D 6) (R 6) [6,160,320,18,65,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1794
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1795 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 120, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 162 324 26 81 40 96 133 261), lower := (rows 7 162 324 26 81 40 96 128 256), losses := [] }

theorem u1795 : Upper (D 6) (R 6) [6,160,320,18,65,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1795
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1796 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 162 324 26 112 33 65 140 268), lower := (rows 7 162 324 26 112 33 65 128 256), losses := [] }

theorem u1796 : Upper (D 6) (R 6) [6,160,320,18,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1796
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1797 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 162 324 26 112 33 68 137 265), lower := (rows 7 162 324 26 112 33 68 128 256), losses := [] }

theorem u1797 : Upper (D 6) (R 6) [6,160,320,18,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1797
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1798 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 88, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 162 324 26 112 33 72 133 261), lower := (rows 7 162 324 26 112 33 72 128 256), losses := [] }

theorem u1798 : Upper (D 6) (R 6) [6,160,320,18,96,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1798
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1799 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 40, targets := 2 },{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,1),(4,2),(4,5)], upper := (rows 7 162 324 44 82 33 65 152 280), lower := (rows 7 162 324 44 82 33 65 128 256), losses := [] }

theorem u1799 : Upper (D 6) (R 6) [6,160,320,36,66,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1799
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1799
end Delivery.IrregularNine14.P06
