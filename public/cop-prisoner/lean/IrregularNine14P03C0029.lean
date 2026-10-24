import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0004

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1740 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 265 208 33 83 147 275), lower := (rows 97 14 164 265 208 33 64 128 256), losses := [] }

theorem u1740 : Upper (D 3) (R 3) [96,12,160,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1740
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1741 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 14 164 265 208 34 81 145 273), lower := (rows 97 14 164 265 208 34 64 128 256), losses := [] }

theorem u1741 : Upper (D 3) (R 3) [96,12,160,257,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1741
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1742 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 14 164 265 208 48 67 131 259), lower := (rows 97 14 164 265 208 48 64 128 256), losses := [] }

theorem u1742 : Upper (D 3) (R 3) [96,12,160,257,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1742
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1743 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 328 145 33 83 147 275), lower := (rows 97 14 164 328 145 33 64 128 256), losses := [] }

theorem u1743 : Upper (D 3) (R 3) [96,12,160,320,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1743
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1744 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 14 164 328 145 34 81 145 273), lower := (rows 97 14 164 328 145 34 64 128 256), losses := [] }

theorem u1744 : Upper (D 3) (R 3) [96,12,160,320,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1744
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1745 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 14 164 328 145 48 67 131 259), lower := (rows 97 14 164 328 145 48 64 128 256), losses := [] }

theorem u1745 : Upper (D 3) (R 3) [96,12,160,320,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1745
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1746 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 273 33 210 146 402), lower := (rows 97 38 76 137 273 33 64 128 256), losses := [] }

theorem u1746 : Upper (D 3) (R 3) [96,36,72,129,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1746
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1747 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 38 76 137 273 34 209 145 401), lower := (rows 97 38 76 137 273 34 64 128 256), losses := [] }

theorem u1747 : Upper (D 3) (R 3) [96,36,72,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1747
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1748 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 76 137 273 48 195 131 387), lower := (rows 97 38 76 137 273 48 64 128 256), losses := [] }

theorem u1748 : Upper (D 3) (R 3) [96,36,72,129,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1748
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1749 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 273 160 83 147 275), lower := (rows 97 38 76 137 273 160 64 128 256), losses := [] }

theorem u1749 : Upper (D 3) (R 3) [96,36,72,129,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1749
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1750 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 274 33 209 145 401), lower := (rows 97 38 76 137 274 33 64 128 256), losses := [] }

theorem u1750 : Upper (D 3) (R 3) [96,36,72,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1750
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1751 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 137 274 48 193 129 385), lower := (rows 97 38 76 137 274 48 64 128 256), losses := [] }

theorem u1751 : Upper (D 3) (R 3) [96,36,72,129,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1751
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1752 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 274 160 81 145 273), lower := (rows 97 38 76 137 274 160 64 128 256), losses := [] }

theorem u1752 : Upper (D 3) (R 3) [96,36,72,129,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1752
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1753 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 137 400 33 83 147 275), lower := (rows 97 38 76 137 400 33 64 128 256), losses := [] }

theorem u1753 : Upper (D 3) (R 3) [96,36,72,129,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1753
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1754 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 76 137 400 34 81 145 273), lower := (rows 97 38 76 137 400 34 64 128 256), losses := [] }

theorem u1754 : Upper (D 3) (R 3) [96,36,72,129,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1754
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1755 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 76 137 400 48 67 131 259), lower := (rows 97 38 76 137 400 48 64 128 256), losses := [] }

theorem u1755 : Upper (D 3) (R 3) [96,36,72,129,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1755
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1756 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 273 33 195 131 387), lower := (rows 97 38 76 152 273 33 64 128 256), losses := [] }

theorem u1756 : Upper (D 3) (R 3) [96,36,72,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1756
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1757 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 152 273 34 193 129 385), lower := (rows 97 38 76 152 273 34 64 128 256), losses := [] }

theorem u1757 : Upper (D 3) (R 3) [96,36,72,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1757
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1758 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 273 160 67 131 259), lower := (rows 97 38 76 152 273 160 64 128 256), losses := [] }

theorem u1758 : Upper (D 3) (R 3) [96,36,72,144,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1758
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1759 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 274 33 193 129 385), lower := (rows 97 38 76 152 274 33 64 128 256), losses := [] }

theorem u1759 : Upper (D 3) (R 3) [96,36,72,144,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1759
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1760 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 152 274 160 65 129 257), lower := (rows 97 38 76 152 274 160 64 128 256), losses := [] }

theorem u1760 : Upper (D 3) (R 3) [96,36,72,144,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1760
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1761 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 265 145 33 210 146 402), lower := (rows 97 38 76 265 145 33 64 128 256), losses := [] }

theorem u1761 : Upper (D 3) (R 3) [96,36,72,257,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1761
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1762 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 38 76 265 145 34 209 145 401), lower := (rows 97 38 76 265 145 34 64 128 256), losses := [] }

theorem u1762 : Upper (D 3) (R 3) [96,36,72,257,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1762
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1763 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 76 265 145 48 195 131 387), lower := (rows 97 38 76 265 145 48 64 128 256), losses := [] }

theorem u1763 : Upper (D 3) (R 3) [96,36,72,257,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1763
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1764 : Route 9 := (fun mask => (mask,id))

def c1764 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1764 : Upper (D 3) (R 3) [96,36,72,257,129,128] 13 := by
  apply FastRouting.sound _ _ [96,36,72,257,129,128] 13 (by decide) (choices 1) [1,2,16] r1764 c1764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u285
  · exact u286
  · exact u287

def b1765 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 265 146 33 209 145 401), lower := (rows 97 38 76 265 146 33 64 128 256), losses := [] }

theorem u1765 : Upper (D 3) (R 3) [96,36,72,257,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1765
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1766 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 265 146 48 193 129 385), lower := (rows 97 38 76 265 146 48 64 128 256), losses := [] }

theorem u1766 : Upper (D 3) (R 3) [96,36,72,257,130,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1766
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1767 : Route 9 := (fun mask => (mask,id))

def c1767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1767 : Upper (D 3) (R 3) [96,36,72,257,130,128] 13 := by
  apply FastRouting.sound _ _ [96,36,72,257,130,128] 13 (by decide) (choices 1) [1,16] r1767 c1767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u288
  · exact u289

def b1768 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 280 145 33 195 131 387), lower := (rows 97 38 76 280 145 33 64 128 256), losses := [] }

theorem u1768 : Upper (D 3) (R 3) [96,36,72,272,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1768
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1769 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 280 145 34 193 129 385), lower := (rows 97 38 76 280 145 34 64 128 256), losses := [] }

theorem u1769 : Upper (D 3) (R 3) [96,36,72,272,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1769
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1770 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 280 145 160 67 131 259), lower := (rows 97 38 76 280 145 160 64 128 256), losses := [] }

theorem u1770 : Upper (D 3) (R 3) [96,36,72,272,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1770
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1771 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 280 146 33 193 129 385), lower := (rows 97 38 76 280 146 33 64 128 256), losses := [] }

theorem u1771 : Upper (D 3) (R 3) [96,36,72,272,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1771
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1772 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 280 146 160 65 129 257), lower := (rows 97 38 76 280 146 160 64 128 256), losses := [] }

theorem u1772 : Upper (D 3) (R 3) [96,36,72,272,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1772
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1773 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 392 145 33 83 147 275), lower := (rows 97 38 76 392 145 33 64 128 256), losses := [] }

theorem u1773 : Upper (D 3) (R 3) [96,36,72,384,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1773
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1774 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 76 392 145 34 81 145 273), lower := (rows 97 38 76 392 145 34 64 128 256), losses := [] }

theorem u1774 : Upper (D 3) (R 3) [96,36,72,384,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1774
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1775 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 76 392 145 48 67 131 259), lower := (rows 97 38 76 392 145 48 64 128 256), losses := [] }

theorem u1775 : Upper (D 3) (R 3) [96,36,72,384,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1775
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1776 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 88 273 33 202 138 394), lower := (rows 97 38 133 88 273 33 64 128 256), losses := [] }

theorem u1776 : Upper (D 3) (R 3) [96,36,129,80,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1776
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1777 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 38 133 88 273 34 201 137 393), lower := (rows 97 38 133 88 273 34 64 128 256), losses := [] }

theorem u1777 : Upper (D 3) (R 3) [96,36,129,80,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1777
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1778 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 133 88 273 40 195 131 387), lower := (rows 97 38 133 88 273 40 64 128 256), losses := [] }

theorem u1778 : Upper (D 3) (R 3) [96,36,129,80,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1778
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1779 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 88 273 160 75 139 267), lower := (rows 97 38 133 88 273 160 64 128 256), losses := [] }

theorem u1779 : Upper (D 3) (R 3) [96,36,129,80,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1779
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1780 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 88 274 33 201 137 393), lower := (rows 97 38 133 88 274 33 64 128 256), losses := [] }

theorem u1780 : Upper (D 3) (R 3) [96,36,129,80,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1780
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1781 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 133 88 274 40 193 129 385), lower := (rows 97 38 133 88 274 40 64 128 256), losses := [] }

theorem u1781 : Upper (D 3) (R 3) [96,36,129,80,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1781
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1782 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 88 274 160 73 137 265), lower := (rows 97 38 133 88 274 160 64 128 256), losses := [] }

theorem u1782 : Upper (D 3) (R 3) [96,36,129,80,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1782
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1783 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 88 400 33 75 139 267), lower := (rows 97 38 133 88 400 33 64 128 256), losses := [] }

theorem u1783 : Upper (D 3) (R 3) [96,36,129,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1783
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1784 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 133 88 400 34 73 137 265), lower := (rows 97 38 133 88 400 34 64 128 256), losses := [] }

theorem u1784 : Upper (D 3) (R 3) [96,36,129,80,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1784
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1785 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 133 88 400 40 67 131 259), lower := (rows 97 38 133 88 400 40 64 128 256), losses := [] }

theorem u1785 : Upper (D 3) (R 3) [96,36,129,80,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1785
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1786 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 152 273 33 74 202 330), lower := (rows 97 38 133 152 273 33 64 128 256), losses := [] }

theorem u1786 : Upper (D 3) (R 3) [96,36,129,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1786
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1787 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 38 133 152 273 34 73 201 329), lower := (rows 97 38 133 152 273 34 64 128 256), losses := [] }

theorem u1787 : Upper (D 3) (R 3) [96,36,129,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1787
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1788 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 38 133 152 273 40 67 195 323), lower := (rows 97 38 133 152 273 40 64 128 256), losses := [] }

theorem u1788 : Upper (D 3) (R 3) [96,36,129,144,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1788
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1789 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 152 273 96 75 139 267), lower := (rows 97 38 133 152 273 96 64 128 256), losses := [] }

theorem u1789 : Upper (D 3) (R 3) [96,36,129,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1789
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1790 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 152 336 33 75 139 267), lower := (rows 97 38 133 152 336 33 64 128 256), losses := [] }

theorem u1790 : Upper (D 3) (R 3) [96,36,129,144,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1790
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1791 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 133 152 336 34 73 137 265), lower := (rows 97 38 133 152 336 34 64 128 256), losses := [] }

theorem u1791 : Upper (D 3) (R 3) [96,36,129,144,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1791
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1792 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 133 152 336 40 67 131 259), lower := (rows 97 38 133 152 336 40 64 128 256), losses := [] }

theorem u1792 : Upper (D 3) (R 3) [96,36,129,144,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1792
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1793 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 200 273 33 90 154 282), lower := (rows 97 38 133 200 273 33 64 128 256), losses := [] }

theorem u1793 : Upper (D 3) (R 3) [96,36,129,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1793
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1794 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 38 133 200 273 34 89 153 281), lower := (rows 97 38 133 200 273 34 64 128 256), losses := [] }

theorem u1794 : Upper (D 3) (R 3) [96,36,129,192,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1794
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1795 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 38 133 200 273 40 83 147 275), lower := (rows 97 38 133 200 273 40 64 128 256), losses := [] }

theorem u1795 : Upper (D 3) (R 3) [96,36,129,192,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1795
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1796 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 38 133 200 273 48 75 139 267), lower := (rows 97 38 133 200 273 48 64 128 256), losses := [] }

theorem u1796 : Upper (D 3) (R 3) [96,36,129,192,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1796
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1797 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 200 274 33 89 153 281), lower := (rows 97 38 133 200 274 33 64 128 256), losses := [] }

theorem u1797 : Upper (D 3) (R 3) [96,36,129,192,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1797
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1798 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 133 200 274 40 81 145 273), lower := (rows 97 38 133 200 274 40 64 128 256), losses := [] }

theorem u1798 : Upper (D 3) (R 3) [96,36,129,192,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1798
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1799 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 133 200 274 48 73 137 265), lower := (rows 97 38 133 200 274 48 64 128 256), losses := [] }

theorem u1799 : Upper (D 3) (R 3) [96,36,129,192,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1799
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1799
end Delivery.IrregularNine14.P03
