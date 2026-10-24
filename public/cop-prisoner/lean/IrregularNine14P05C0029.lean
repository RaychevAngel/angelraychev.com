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

def b1740 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 133 268 25 36 96 138 266), lower := (rows 35 82 133 268 25 36 96 128 256), losses := [] }

theorem u1740 : Upper (D 5) (R 5) [34,80,129,260,9,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1740
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1741 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 66, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 35 82 134 268 21 40 65 168 296), lower := (rows 35 82 134 268 21 40 65 128 256), losses := [] }

theorem u1741 : Upper (D 5) (R 5) [34,80,130,260,5,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1741
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1742 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 148, targets := 8 }], pairs := [(2,3),(4,3)], upper := (rows 35 82 134 268 21 40 72 161 289), lower := (rows 35 82 134 268 21 40 72 128 256), losses := [] }

theorem u1742 : Upper (D 5) (R 5) [34,80,130,260,5,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1742
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1743 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 134 268 21 40 96 137 265), lower := (rows 35 82 134 268 21 40 96 128 256), losses := [] }

theorem u1743 : Upper (D 5) (R 5) [34,80,130,260,5,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1743
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1744 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 66, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 35 82 134 268 25 36 65 168 296), lower := (rows 35 82 134 268 25 36 65 128 256), losses := [] }

theorem u1744 : Upper (D 5) (R 5) [34,80,130,260,9,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1744
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1745 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 82 134 268 25 36 72 161 289), lower := (rows 35 82 134 268 25 36 72 128 256), losses := [] }

theorem u1745 : Upper (D 5) (R 5) [34,80,130,260,9,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1745
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1746 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 134 268 25 36 96 137 265), lower := (rows 35 82 134 268 25 36 96 128 256), losses := [] }

theorem u1746 : Upper (D 5) (R 5) [34,80,130,260,9,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1746
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1747 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 40 }], pairs := [(1,3),(1,5)], upper := (rows 49 67 133 266 22 40 68 168 296), lower := (rows 49 67 133 266 22 40 68 128 256), losses := [] }

theorem u1747 : Upper (D 5) (R 5) [48,65,129,258,6,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1747
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1748 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 132, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 49 67 133 266 22 40 72 164 292), lower := (rows 49 67 133 266 22 40 72 128 256), losses := [] }

theorem u1748 : Upper (D 5) (R 5) [48,65,129,258,6,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1748
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1749 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 49 67 133 266 22 40 96 140 268), lower := (rows 49 67 133 266 22 40 96 128 256), losses := [] }

theorem u1749 : Upper (D 5) (R 5) [48,65,129,258,6,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1749
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1750 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 66, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 49 67 133 296 26 36 66 140 268), lower := (rows 49 67 133 296 26 36 66 128 256), losses := [] }

theorem u1750 : Upper (D 5) (R 5) [48,65,129,288,10,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1750
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1751 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 66, targets := 8 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,3),(1,5)], upper := (rows 49 67 133 296 26 36 68 138 266), lower := (rows 49 67 133 296 26 36 68 128 256), losses := [] }

theorem u1751 : Upper (D 5) (R 5) [48,65,129,288,10,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1751
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1752 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 49 67 133 296 26 36 72 134 262), lower := (rows 49 67 133 296 26 36 72 128 256), losses := [] }

theorem u1752 : Upper (D 5) (R 5) [48,65,129,288,10,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1752
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1753 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 66, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 49 67 134 296 26 36 65 140 268), lower := (rows 49 67 134 296 26 36 65 128 256), losses := [] }

theorem u1753 : Upper (D 5) (R 5) [48,65,130,288,10,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1753
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1754 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 49 67 134 296 26 36 68 137 265), lower := (rows 49 67 134 296 26 36 68 128 256), losses := [] }

theorem u1754 : Upper (D 5) (R 5) [48,65,130,288,10,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1754
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1755 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 49 67 134 296 26 36 72 133 261), lower := (rows 49 67 134 296 26 36 72 128 256), losses := [] }

theorem u1755 : Upper (D 5) (R 5) [48,65,130,288,10,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1755
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1756 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 66, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 49 67 140 296 26 36 65 134 262), lower := (rows 49 67 140 296 26 36 65 128 256), losses := [] }

theorem u1756 : Upper (D 5) (R 5) [48,65,136,288,10,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1756
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1757 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 66, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 49 67 140 296 26 36 66 133 261), lower := (rows 49 67 140 296 26 36 66 128 256), losses := [] }

theorem u1757 : Upper (D 5) (R 5) [48,65,136,288,10,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1757
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1758 : PairBound 9 := { available := 3, camps := [], pairs := [(1,3),(1,5)], upper := (rows 49 67 140 296 26 36 68 131 259), lower := (rows 49 67 140 296 26 36 68 128 256), losses := [{ target := 3, region := (rows 1 3 4 0 16 100 100 131 259), good := (rows 499 483 228 352 402 100 100 128 256) },{ target := 5, region := (rows 1 3 20 8 16 0 117 131 259), good := (rows 471 451 204 328 478 68 68 128 256) }] }

theorem u1758 : Upper (D 5) (R 5) [48,65,136,288,10,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1758
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1759 : PairBound 9 := { available := 40, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 49 70 134 266 21 40 65 168 296), lower := (rows 49 70 134 266 21 40 65 128 256), losses := [] }

theorem u1759 : Upper (D 5) (R 5) [48,68,130,258,5,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1759
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1760 : PairBound 9 := { available := 33, camps := [], pairs := [(0,1),(4,1)], upper := (rows 49 70 134 266 21 40 72 161 289), lower := (rows 49 70 134 266 21 40 72 128 256), losses := [{ target := 1, region := (rows 11 0 4 8 22 104 104 235 363), good := (rows 497 501 405 505 405 489 489 128 256) }] }

theorem u1760 : Upper (D 5) (R 5) [48,68,130,258,5,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1760
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1761 : PairBound 9 := { available := 9, camps := [], pairs := [(1,0),(1,3)], upper := (rows 49 70 134 266 21 40 96 137 265), lower := (rows 49 70 134 266 21 40 96 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 40 105 128 256), good := (rows 114 70 134 362 86 104 96 128 256) },{ target := 3, region := (rows 1 18 4 0 16 32 97 128 256), good := (rows 115 70 134 258 87 96 96 128 256) }] }

theorem u1761 : Upper (D 5) (R 5) [48,68,130,258,5,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1761
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1762 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 49 70 164 268 19 40 65 138 266), lower := (rows 49 70 164 268 19 40 65 128 256), losses := [] }

theorem u1762 : Upper (D 5) (R 5) [48,68,160,260,3,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1762
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1763 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 49 70 164 268 19 40 66 137 265), lower := (rows 49 70 164 268 19 40 66 128 256), losses := [] }

theorem u1763 : Upper (D 5) (R 5) [48,68,160,260,3,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1763
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1764 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 1 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,0),(1,5)], upper := (rows 49 70 164 268 19 40 72 131 259), lower := (rows 49 70 164 268 19 40 72 128 256), losses := [] }

theorem u1764 : Upper (D 5) (R 5) [48,68,160,260,3,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1764
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1765 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 52 104 146 33 332 396 268), lower := (rows 7 11 52 104 146 33 64 128 256), losses := [] }

theorem u1765 : Upper (D 5) (R 5) [6,9,48,96,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1765
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1766 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 400, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 11 52 104 146 36 329 393 265), lower := (rows 7 11 52 104 146 36 64 128 256), losses := [] }

theorem u1766 : Upper (D 5) (R 5) [6,9,48,96,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1766
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1767 : PairBound 9 := { available := 261, camps := [{ cop := 6, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 52 104 146 40 325 389 261), lower := (rows 7 11 52 104 146 40 64 128 256), losses := [] }

theorem u1767 : Upper (D 5) (R 5) [6,9,48,96,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1767
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1768 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 360, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 52 104 146 288 77 141 269), lower := (rows 7 11 52 104 146 288 64 128 256), losses := [] }

theorem u1768 : Upper (D 5) (R 5) [6,9,48,96,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1768
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1769 : PairBound 9 := { available := 262, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 11 52 104 152 33 326 390 262), lower := (rows 7 11 52 104 152 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 50 32 67 131 259), good := (rows 470 478 60 124 156 508 64 128 256) }] }

theorem u1769 : Upper (D 5) (R 5) [6,9,48,96,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1769
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1770 : PairBound 9 := { available := 261, camps := [], pairs := [(2,1),(3,1)], upper := (rows 7 11 52 104 152 34 325 389 261), lower := (rows 7 11 52 104 152 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 44 40 50 32 67 131 259), good := (rows 469 477 60 124 156 508 64 128 256) }] }

theorem u1770 : Upper (D 5) (R 5) [6,9,48,96,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1770
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1771 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 52 104 152 36 323 387 259), lower := (rows 7 11 52 104 152 36 64 128 256), losses := [] }

theorem u1771 : Upper (D 5) (R 5) [6,9,48,96,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1771
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1772 : PairBound 9 := { available := 7, camps := [], pairs := [(4,5)], upper := (rows 7 11 52 104 152 288 71 135 263), lower := (rows 7 11 52 104 152 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 18 0 65 129 257), good := (rows 471 475 20 72 152 256 64 128 256) }] }

theorem u1772 : Upper (D 5) (R 5) [6,9,48,96,136,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1772
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1773 : Route 9 := (fun mask => (mask,id))

def c1773 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1773 : Upper (D 5) (R 5) [6,9,48,96,384,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,384,1] 13 (by decide) (choices 1) [2,4,8] r1773 c1773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u88
  · exact u89
  · exact u90

def b1774 : PairBound 9 := { available := 13, camps := [], pairs := [(2,1),(3,1)], upper := (rows 7 11 52 104 400 34 77 141 269), lower := (rows 7 11 52 104 400 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 44 40 51 32 66 130 258), good := (rows 469 477 60 124 400 508 64 128 256) }] }

theorem u1774 : Upper (D 5) (R 5) [6,9,48,96,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1774
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1775 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 52 104 400 36 75 139 267), lower := (rows 7 11 52 104 400 36 64 128 256), losses := [] }

theorem u1775 : Upper (D 5) (R 5) [6,9,48,96,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1775
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1776 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 52 104 400 40 71 135 263), lower := (rows 7 11 52 104 400 40 64 128 256), losses := [] }

theorem u1776 : Upper (D 5) (R 5) [6,9,48,96,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1776
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1777 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 200, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 52 200 274 33 108 172 300), lower := (rows 7 11 52 200 274 33 64 128 256), losses := [] }

theorem u1777 : Upper (D 5) (R 5) [6,9,48,192,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1777
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1778 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 52 200 274 36 105 169 297), lower := (rows 7 11 52 200 274 36 64 128 256), losses := [] }

theorem u1778 : Upper (D 5) (R 5) [6,9,48,192,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1778
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1779 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(2,0),(3,1)], upper := (rows 7 11 52 200 274 40 101 165 293), lower := (rows 7 11 52 200 274 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 42 64 128 256), good := (rows 38 42 52 232 310 40 64 128 256) }] }

theorem u1779 : Upper (D 5) (R 5) [6,9,48,192,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1779
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1780 : Route 9 := (fun mask => (mask,id))

def c1780 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1780 : Upper (D 5) (R 5) [6,9,48,192,264,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,264,1] 13 (by decide) (choices 1) [2,4,32] r1780 c1780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u91
  · exact u92
  · exact u93

def r1781 : Route 9 := (fun mask => (mask,id))

def c1781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1781 : Upper (D 5) (R 5) [6,9,48,192,264,2] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,264,2] 13 (by decide) (choices 1) [1,4,32] r1781 c1781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u94
  · exact u95
  · exact u96

def b1782 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 52 200 280 36 99 163 291), lower := (rows 7 11 52 200 280 36 64 128 256), losses := [] }

theorem u1782 : Upper (D 5) (R 5) [6,9,48,192,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1782
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1783 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 84 168 50 33 332 396 268), lower := (rows 7 11 84 168 50 33 64 128 256), losses := [] }

theorem u1783 : Upper (D 5) (R 5) [6,9,80,160,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1783
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1784 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 424, targets := 2 }], pairs := [(3,1),(4,0)], upper := (rows 7 11 84 168 50 36 329 393 265), lower := (rows 7 11 84 168 50 36 64 128 256), losses := [] }

theorem u1784 : Upper (D 5) (R 5) [6,9,80,160,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1784
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1785 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 325, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 11 84 168 50 40 325 389 261), lower := (rows 7 11 84 168 50 40 64 128 256), losses := [] }

theorem u1785 : Upper (D 5) (R 5) [6,9,80,160,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1785
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1786 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 424, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 84 168 50 288 77 141 269), lower := (rows 7 11 84 168 50 288 64 128 256), losses := [] }

theorem u1786 : Upper (D 5) (R 5) [6,9,80,160,34,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1786
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1787 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 168, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 11 84 168 274 33 108 172 300), lower := (rows 7 11 84 168 274 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 59 16 35 81 145 273), good := (rows 493 489 476 168 508 489 64 128 256) }] }

theorem u1787 : Upper (D 5) (R 5) [6,9,80,160,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1787
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1788 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 168, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 11 84 168 274 36 105 169 297), lower := (rows 7 11 84 168 274 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 27 16 53 67 131 259), good := (rows 493 489 124 168 508 36 64 128 256) }] }

theorem u1788 : Upper (D 5) (R 5) [6,9,80,160,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1788
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1789 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 84 168 274 40 101 165 293), lower := (rows 7 11 84 168 274 40 64 128 256), losses := [] }

theorem u1789 : Upper (D 5) (R 5) [6,9,80,160,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1789
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1790 : Route 9 := (fun mask => (mask,id))

def c1790 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1790 : Upper (D 5) (R 5) [6,9,80,160,264,1] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,264,1] 13 (by decide) (choices 1) [2,4,32] r1790 c1790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u97
  · exact u98
  · exact u99

def r1791 : Route 9 := (fun mask => (mask,id))

def c1791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1791 : Upper (D 5) (R 5) [6,9,80,160,264,2] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,264,2] 13 (by decide) (choices 1) [1,4,32] r1791 c1791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u100
  · exact u101
  · exact u102

def r1792 : Route 9 := (fun mask => (mask,id))

def c1792 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1792 : Upper (D 5) (R 5) [6,9,80,160,264,4] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,264,4] 13 (by decide) (choices 1) [1,2,32] r1792 c1792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u103
  · exact u104
  · exact u105

def r1793 : Route 9 := (fun mask => (mask,id))

def c1793 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1793 : Upper (D 5) (R 5) [6,9,80,160,288,1] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,288,1] 13 (by decide) (choices 1) [2,4,8] r1793 c1793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u106
  · exact u107
  · exact u108

def r1794 : Route 9 := (fun mask => (mask,id))

def c1794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1794 : Upper (D 5) (R 5) [6,9,80,160,288,2] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,288,2] 13 (by decide) (choices 1) [1,4,8] r1794 c1794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u109
  · exact u110
  · exact u111

def r1795 : Route 9 := (fun mask => (mask,id))

def c1795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1795 : Upper (D 5) (R 5) [6,9,80,160,288,4] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,288,4] 13 (by decide) (choices 1) [1,2,8] r1795 c1795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u112
  · exact u113
  · exact u114

def b1796 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 84 168 304 40 71 135 263), lower := (rows 7 11 84 168 304 40 64 128 256), losses := [] }

theorem u1796 : Upper (D 5) (R 5) [6,9,80,160,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1796
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1797 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 84 392 50 33 108 172 300), lower := (rows 7 11 84 392 50 33 64 128 256), losses := [] }

theorem u1797 : Upper (D 5) (R 5) [6,9,80,384,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1797
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1798 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 424, targets := 2 }], pairs := [(3,1),(4,0)], upper := (rows 7 11 84 392 50 36 105 169 297), lower := (rows 7 11 84 392 50 36 64 128 256), losses := [] }

theorem u1798 : Upper (D 5) (R 5) [6,9,80,384,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1798
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1799 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 84 392 50 40 101 165 293), lower := (rows 7 11 84 392 50 40 64 128 256), losses := [] }

theorem u1799 : Upper (D 5) (R 5) [6,9,80,384,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1799
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1799
end Delivery.IrregularNine14.P05
