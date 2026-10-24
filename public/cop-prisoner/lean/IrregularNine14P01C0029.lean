import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0003

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1740 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 164 138 80 34 89 153 281), lower := (rows 277 98 164 138 80 34 64 128 256), losses := [] }

theorem u1740 : Upper (D 1) (R 1) [276,96,160,130,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1740
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1741 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 277 98 164 138 80 40 83 147 275), lower := (rows 277 98 164 138 80 40 64 128 256), losses := [] }

theorem u1741 : Upper (D 1) (R 1) [276,96,160,130,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1741
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1742 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 164 138 80 48 75 139 267), lower := (rows 277 98 164 138 80 48 64 128 256), losses := [] }

theorem u1742 : Upper (D 1) (R 1) [276,96,160,130,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1742
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1743 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 277 98 164 152 18 33 74 202 330), lower := (rows 277 98 164 152 18 33 64 128 256), losses := [] }

theorem u1743 : Upper (D 1) (R 1) [276,96,160,144,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1743
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1744 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 164 152 18 34 73 201 329), lower := (rows 277 98 164 152 18 34 64 128 256), losses := [] }

theorem u1744 : Upper (D 1) (R 1) [276,96,160,144,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1744
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1745 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 277 98 164 152 18 40 67 195 323), lower := (rows 277 98 164 152 18 40 64 128 256), losses := [] }

theorem u1745 : Upper (D 1) (R 1) [276,96,160,144,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1745
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1746 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 164 152 18 96 75 139 267), lower := (rows 277 98 164 152 18 96 64 128 256), losses := [] }

theorem u1746 : Upper (D 1) (R 1) [276,96,160,144,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1746
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1747 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 277 98 164 152 80 33 74 138 266), lower := (rows 277 98 164 152 80 33 64 128 256), losses := [] }

theorem u1747 : Upper (D 1) (R 1) [276,96,160,144,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1747
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1748 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 164 152 80 34 75 139 267), lower := (rows 277 98 164 152 80 34 64 128 256), losses := [] }

theorem u1748 : Upper (D 1) (R 1) [276,96,160,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1748
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1749 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 277 98 164 152 80 40 67 131 259), lower := (rows 277 98 164 152 80 40 64 128 256), losses := [] }

theorem u1749 : Upper (D 1) (R 1) [276,96,160,144,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1749
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1750 : PairBound 9 := { available := 26, camps := [], pairs := [], upper := (rows 277 98 164 200 18 33 90 154 282), lower := (rows 277 98 164 200 18 33 64 128 256), losses := [] }

theorem u1750 : Upper (D 1) (R 1) [276,96,160,192,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1750
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1751 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 164 200 18 34 89 153 281), lower := (rows 277 98 164 200 18 34 64 128 256), losses := [] }

theorem u1751 : Upper (D 1) (R 1) [276,96,160,192,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1751
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1752 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 277 98 164 200 18 40 83 147 275), lower := (rows 277 98 164 200 18 40 64 128 256), losses := [] }

theorem u1752 : Upper (D 1) (R 1) [276,96,160,192,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1752
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1753 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 50, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 164 200 18 48 75 139 267), lower := (rows 277 98 164 200 18 48 64 128 256), losses := [] }

theorem u1753 : Upper (D 1) (R 1) [276,96,160,192,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1753
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1754 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 14 88 144 34 224 224 480), lower := (rows 305 7 14 88 144 34 64 128 256), losses := [] }

theorem u1754 : Upper (D 1) (R 1) [304,5,10,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1754
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1755 : Route 9 := (fun mask => (mask,id))

def c1755 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1755 : Upper (D 1) (R 1) [304,5,10,80,128,64] 13 := by
  apply FastRouting.sound _ _ [304,5,10,80,128,64] 13 (by decide) (choices 1) [2,32,128] r1755 c1755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u198
  · exact u199
  · exact u200

def b1756 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 7 14 88 144 160 98 226 354), lower := (rows 305 7 14 88 144 160 64 128 256), losses := [] }

theorem u1756 : Upper (D 1) (R 1) [304,5,10,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1756
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1757 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 14 200 18 96 240 176 432), lower := (rows 305 7 14 200 18 96 64 128 256), losses := [] }

theorem u1757 : Upper (D 1) (R 1) [304,5,10,192,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1757
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1758 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 14 200 48 96 210 146 402), lower := (rows 305 7 14 200 48 96 64 128 256), losses := [] }

theorem u1758 : Upper (D 1) (R 1) [304,5,10,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1758
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1759 : Route 9 := (fun mask => (mask,id))

def c1759 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1759 : Upper (D 1) (R 1) [304,5,10,192,64,128] 13 := by
  apply FastRouting.sound _ _ [304,5,10,192,64,128] 13 (by decide) (choices 1) [2,16,32] r1759 c1759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u201
  · exact u202
  · exact u203

def b1760 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 70 88 144 34 232 168 424), lower := (rows 305 7 70 88 144 34 64 128 256), losses := [] }

theorem u1760 : Upper (D 1) (R 1) [304,5,66,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1760
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1761 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 7 70 88 144 40 226 162 418), lower := (rows 305 7 70 88 144 40 64 128 256), losses := [] }

theorem u1761 : Upper (D 1) (R 1) [304,5,66,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1761
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1762 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 7 70 88 144 160 106 170 298), lower := (rows 305 7 70 88 144 160 64 128 256), losses := [] }

theorem u1762 : Upper (D 1) (R 1) [304,5,66,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1762
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1763 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 70 152 80 34 232 168 424), lower := (rows 305 7 70 152 80 34 64 128 256), losses := [] }

theorem u1763 : Upper (D 1) (R 1) [304,5,66,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1763
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1764 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 7 70 152 80 40 226 162 418), lower := (rows 305 7 70 152 80 40 64 128 256), losses := [] }

theorem u1764 : Upper (D 1) (R 1) [304,5,66,144,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1764
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1765 : Route 9 := (fun mask => (mask,id))

def c1765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1765 : Upper (D 1) (R 1) [304,5,66,144,64,128] 13 := by
  apply FastRouting.sound _ _ [304,5,66,144,64,128] 13 (by decide) (choices 1) [2,8,32] r1765 c1765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u204
  · exact u205
  · exact u206

def b1766 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 70 200 18 160 120 184 312), lower := (rows 305 7 70 200 18 160 64 128 256), losses := [] }

theorem u1766 : Upper (D 1) (R 1) [304,5,66,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1766
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1767 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 7 70 200 24 160 114 178 306), lower := (rows 305 7 70 200 24 160 64 128 256), losses := [] }

theorem u1767 : Upper (D 1) (R 1) [304,5,66,192,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1767
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1768 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 70 200 48 160 90 154 282), lower := (rows 305 7 70 200 48 160 64 128 256), losses := [] }

theorem u1768 : Upper (D 1) (R 1) [304,5,66,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1768
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1769 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 76 138 18 96 240 176 432), lower := (rows 305 7 76 138 18 96 64 128 256), losses := [] }

theorem u1769 : Upper (D 1) (R 1) [304,5,72,130,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1769
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1770 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 76 138 18 160 112 240 368), lower := (rows 305 7 76 138 18 160 64 128 256), losses := [] }

theorem u1770 : Upper (D 1) (R 1) [304,5,72,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1770
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1771 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 76 138 48 96 210 146 402), lower := (rows 305 7 76 138 48 96 64 128 256), losses := [] }

theorem u1771 : Upper (D 1) (R 1) [304,5,72,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1771
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1772 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 76 138 48 160 82 210 338), lower := (rows 305 7 76 138 48 160 64 128 256), losses := [] }

theorem u1772 : Upper (D 1) (R 1) [304,5,72,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1772
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1773 : Route 9 := (fun mask => (mask,id))

def c1773 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1773 : Upper (D 1) (R 1) [304,5,72,130,64,128] 13 := by
  apply FastRouting.sound _ _ [304,5,72,130,64,128] 13 (by decide) (choices 1) [2,16,32] r1773 c1773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u207
  · exact u208
  · exact u209

def b1774 : PairBound 9 := { available := 162, camps := [], pairs := [(3,6)], upper := (rows 305 7 76 152 80 34 226 162 418), lower := (rows 305 7 76 152 80 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 16 34 0 162 290), good := (rows 441 431 12 152 16 418 0 128 256) }] }

theorem u1774 : Upper (D 1) (R 1) [304,5,72,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1774
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1775 : Route 9 := (fun mask => (mask,id))

def c1775 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1775 : Upper (D 1) (R 1) [304,5,72,144,64,128] 13 := by
  apply FastRouting.sound _ _ [304,5,72,144,64,128] 13 (by decide) (choices 1) [2,32] r1775 c1775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u210
  · exact u211

def b1776 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 7 196 88 18 34 232 168 424), lower := (rows 305 7 196 88 18 34 64 128 256), losses := [] }

theorem u1776 : Upper (D 1) (R 1) [304,5,192,80,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1776
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1777 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 7 196 88 18 40 226 162 418), lower := (rows 305 7 196 88 18 40 64 128 256), losses := [] }

theorem u1777 : Upper (D 1) (R 1) [304,5,192,80,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1777
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1778 : Route 9 := (fun mask => (mask,id))

def c1778 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1778 : Upper (D 1) (R 1) [304,5,192,80,2,128] 13 := by
  apply FastRouting.sound _ _ [304,5,192,80,2,128] 13 (by decide) (choices 1) [2,8,32] r1778 c1778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u212
  · exact u213
  · exact u214

def b1779 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 7 88 144 34 224 224 480), lower := (rows 305 14 7 88 144 34 64 128 256), losses := [] }

theorem u1779 : Upper (D 1) (R 1) [304,12,3,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1779
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1780 : Route 9 := (fun mask => (mask,id))

def c1780 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1780 : Upper (D 1) (R 1) [304,12,3,80,128,64] 13 := by
  apply FastRouting.sound _ _ [304,12,3,80,128,64] 13 (by decide) (choices 1) [2,32,128] r1780 c1780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u215
  · exact u216
  · exact u217

def b1781 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 14 7 88 144 160 98 226 354), lower := (rows 305 14 7 88 144 160 64 128 256), losses := [] }

theorem u1781 : Upper (D 1) (R 1) [304,12,3,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1781
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1782 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 7 200 18 96 240 176 432), lower := (rows 305 14 7 200 18 96 64 128 256), losses := [] }

theorem u1782 : Upper (D 1) (R 1) [304,12,3,192,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1782
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1783 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 7 200 48 96 210 146 402), lower := (rows 305 14 7 200 48 96 64 128 256), losses := [] }

theorem u1783 : Upper (D 1) (R 1) [304,12,3,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1783
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1784 : Route 9 := (fun mask => (mask,id))

def c1784 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1784 : Upper (D 1) (R 1) [304,12,3,192,64,128] 13 := by
  apply FastRouting.sound _ _ [304,12,3,192,64,128] 13 (by decide) (choices 1) [2,16,32] r1784 c1784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u218
  · exact u219
  · exact u220

def b1785 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 22 73 144 34 224 224 480), lower := (rows 305 14 22 73 144 34 64 128 256), losses := [] }

theorem u1785 : Upper (D 1) (R 1) [304,12,18,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1785
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1786 : Route 9 := (fun mask => (mask,id))

def c1786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1786 : Upper (D 1) (R 1) [304,12,18,65,128,64] 13 := by
  apply FastRouting.sound _ _ [304,12,18,65,128,64] 13 (by decide) (choices 1) [2,32,128] r1786 c1786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u221
  · exact u222
  · exact u223

def b1787 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 14 22 73 144 160 98 226 354), lower := (rows 305 14 22 73 144 160 64 128 256), losses := [] }

theorem u1787 : Upper (D 1) (R 1) [304,12,18,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1787
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1788 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 14 22 104 144 33 194 194 450), lower := (rows 305 14 22 104 144 33 64 128 256), losses := [] }

theorem u1788 : Upper (D 1) (R 1) [304,12,18,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1788
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1789 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 22 104 144 34 193 193 449), lower := (rows 305 14 22 104 144 34 64 128 256), losses := [] }

theorem u1789 : Upper (D 1) (R 1) [304,12,18,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1789
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1790 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 22 104 144 96 195 131 387), lower := (rows 305 14 22 104 144 96 64 128 256), losses := [] }

theorem u1790 : Upper (D 1) (R 1) [304,12,18,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1790
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1791 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 14 22 104 144 160 67 195 323), lower := (rows 305 14 22 104 144 160 64 128 256), losses := [] }

theorem u1791 : Upper (D 1) (R 1) [304,12,18,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1791
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1792 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 69 138 18 96 240 176 432), lower := (rows 305 14 69 138 18 96 64 128 256), losses := [] }

theorem u1792 : Upper (D 1) (R 1) [304,12,65,130,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1792
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1793 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 69 138 18 160 112 240 368), lower := (rows 305 14 69 138 18 160 64 128 256), losses := [] }

theorem u1793 : Upper (D 1) (R 1) [304,12,65,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1793
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1794 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 138 48 96 210 146 402), lower := (rows 305 14 69 138 48 96 64 128 256), losses := [] }

theorem u1794 : Upper (D 1) (R 1) [304,12,65,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1794
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1795 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 138 48 160 82 210 338), lower := (rows 305 14 69 138 48 160 64 128 256), losses := [] }

theorem u1795 : Upper (D 1) (R 1) [304,12,65,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1795
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1796 : Route 9 := (fun mask => (mask,id))

def c1796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1796 : Upper (D 1) (R 1) [304,12,65,130,64,128] 13 := by
  apply FastRouting.sound _ _ [304,12,65,130,64,128] 13 (by decide) (choices 1) [2,16,32] r1796 c1796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u224
  · exact u225
  · exact u226

def b1797 : PairBound 9 := { available := 162, camps := [], pairs := [(2,4)], upper := (rows 305 14 69 152 80 34 226 162 418), lower := (rows 305 14 69 152 80 34 64 128 256), losses := [{ target := 4, region := (rows 1 2 5 8 0 34 98 162 290), good := (rows 485 494 69 136 64 482 64 128 256) }] }

theorem u1797 : Upper (D 1) (R 1) [304,12,65,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1797
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1798 : Route 9 := (fun mask => (mask,id))

def c1798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1798 : Upper (D 1) (R 1) [304,12,65,144,64,128] 13 := by
  apply FastRouting.sound _ _ [304,12,65,144,64,128] 13 (by decide) (choices 1) [2,32] r1798 c1798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u227
  · exact u228

def b1799 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 14 70 152 80 33 226 162 418), lower := (rows 305 14 70 152 80 33 64 128 256), losses := [] }

theorem u1799 : Upper (D 1) (R 1) [304,12,66,144,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1799
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1799
end Delivery.IrregularNine14.P01
