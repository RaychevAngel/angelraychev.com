import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0009
import IrregularNine14P00C0010

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1740 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 140 296 18 225 193 193 449), lower := (rows 113 22 140 296 18 32 64 128 256), losses := [] }

theorem u1740 : Upper (D 0) (R 0) [112,20,136,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1740
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1741 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 140 296 80 163 195 131 387), lower := (rows 113 22 140 296 80 32 64 128 256), losses := [] }

theorem u1741 : Upper (D 0) (R 0) [112,20,136,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1741
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1742 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 140 296 144 99 67 195 323), lower := (rows 113 22 140 296 144 32 64 128 256), losses := [] }

theorem u1742 : Upper (D 0) (R 0) [112,20,136,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1742
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1743 : Route 9 := (fun mask => (mask,id))

def c1743 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1743 : Upper (D 0) (R 0) [112,20,160,129,1] 13 := by
  apply FastRouting.sound _ _ [112,20,160,129,1] 13 (by decide) (choices 1) [2,8,64,256] r1743 c1743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u580
  · exact u581
  · exact u582
  · exact u583

def b1744 : PairBound 9 := { available := 329, camps := [], pairs := [], upper := (rows 113 22 164 137 18 361 329 457 329), lower := (rows 113 22 164 137 18 32 64 128 256), losses := [] }

theorem u1744 : Upper (D 0) (R 0) [112,20,160,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1744
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1745 : PairBound 9 := { available := 323, camps := [], pairs := [], upper := (rows 113 22 164 137 24 355 323 451 323), lower := (rows 113 22 164 137 24 32 64 128 256), losses := [] }

theorem u1745 : Upper (D 0) (R 0) [112,20,160,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1745
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1746 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 137 80 299 331 395 267), lower := (rows 113 22 164 137 80 32 64 128 256), losses := [] }

theorem u1746 : Upper (D 0) (R 0) [112,20,160,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1746
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1747 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 113 22 164 137 272 107 75 203 331), lower := (rows 113 22 164 137 272 32 64 128 256), losses := [] }

theorem u1747 : Upper (D 0) (R 0) [112,20,160,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1747
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1748 : Route 9 := (fun mask => (mask,id))

def c1748 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1748 : Upper (D 0) (R 0) [112,20,160,192,1] 13 := by
  apply FastRouting.sound _ _ [112,20,160,192,1] 13 (by decide) (choices 1) [1,2,8,256] r1748 c1748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u584
  · exact u585
  · exact u586
  · exact u587

def b1749 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 113 22 164 200 18 297 329 393 265), lower := (rows 113 22 164 200 18 32 64 128 256), losses := [] }

theorem u1749 : Upper (D 0) (R 0) [112,20,160,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1749
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1750 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 113 22 164 200 24 291 323 387 259), lower := (rows 113 22 164 200 24 32 64 128 256), losses := [] }

theorem u1750 : Upper (D 0) (R 0) [112,20,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1750
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1751 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 113 22 164 200 272 43 75 139 267), lower := (rows 113 22 164 200 272 32 64 128 256), losses := [] }

theorem u1751 : Upper (D 0) (R 0) [112,20,160,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1751
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1752 : Route 9 := (fun mask => (mask,id))

def c1752 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1752 : Upper (D 0) (R 0) [112,20,160,257,1] 13 := by
  apply FastRouting.sound _ _ [112,20,160,257,1] 13 (by decide) (choices 1) [2,8,64,128] r1752 c1752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u588
  · exact u589
  · exact u590
  · exact u591

def b1753 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 113 22 164 265 18 233 201 201 457), lower := (rows 113 22 164 265 18 32 64 128 256), losses := [] }

theorem u1753 : Upper (D 0) (R 0) [112,20,160,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1753
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1754 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 164 265 24 227 195 195 451), lower := (rows 113 22 164 265 24 32 64 128 256), losses := [] }

theorem u1754 : Upper (D 0) (R 0) [112,20,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1754
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1755 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 265 80 171 203 139 395), lower := (rows 113 22 164 265 80 32 64 128 256), losses := [] }

theorem u1755 : Upper (D 0) (R 0) [112,20,160,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1755
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1756 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 164 265 144 107 75 203 331), lower := (rows 113 22 164 265 144 32 64 128 256), losses := [] }

theorem u1756 : Upper (D 0) (R 0) [112,20,160,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1756
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1757 : Route 9 := (fun mask => (mask,id))

def c1757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1757 : Upper (D 0) (R 0) [112,20,160,258,1] 13 := by
  apply FastRouting.sound _ _ [112,20,160,258,1] 13 (by decide) (choices 1) [1,8,64,128] r1757 c1757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u592
  · exact u593
  · exact u594
  · exact u595

def b1758 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 164 266 24 225 193 193 449), lower := (rows 113 22 164 266 24 32 64 128 256), losses := [] }

theorem u1758 : Upper (D 0) (R 0) [112,20,160,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1758
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1759 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 266 80 169 201 137 393), lower := (rows 113 22 164 266 80 32 64 128 256), losses := [] }

theorem u1759 : Upper (D 0) (R 0) [112,20,160,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1759
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1760 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 164 266 144 105 73 201 329), lower := (rows 113 22 164 266 144 32 64 128 256), losses := [] }

theorem u1760 : Upper (D 0) (R 0) [112,20,160,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1760
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1761 : Route 9 := (fun mask => (mask,id))

def c1761 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1761 : Upper (D 0) (R 0) [112,20,160,320,1] 13 := by
  apply FastRouting.sound _ _ [112,20,160,320,1] 13 (by decide) (choices 1) [1,2,8,128] r1761 c1761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u596
  · exact u597
  · exact u598
  · exact u599

def b1762 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 113 22 164 328 18 169 201 137 393), lower := (rows 113 22 164 328 18 32 64 128 256), losses := [] }

theorem u1762 : Upper (D 0) (R 0) [112,20,160,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1762
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1763 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 22 164 328 24 163 195 131 387), lower := (rows 113 22 164 328 24 32 64 128 256), losses := [] }

theorem u1763 : Upper (D 0) (R 0) [112,20,160,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1763
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1764 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 164 328 144 43 75 139 267), lower := (rows 113 22 164 328 144 32 64 128 256), losses := [] }

theorem u1764 : Upper (D 0) (R 0) [112,20,160,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1764
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1765 : Route 9 := (fun mask => (mask,id))

def c1765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1765 : Upper (D 0) (R 0) [112,20,160,384,1] 13 := by
  apply FastRouting.sound _ _ [112,20,160,384,1] 13 (by decide) (choices 1) [1,2,8,64] r1765 c1765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u600
  · exact u601
  · exact u602
  · exact u603

def b1766 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 113 22 164 392 18 105 73 201 329), lower := (rows 113 22 164 392 18 32 64 128 256), losses := [] }

theorem u1766 : Upper (D 0) (R 0) [112,20,160,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1766
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1767 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 22 164 392 24 99 67 195 323), lower := (rows 113 22 164 392 24 32 64 128 256), losses := [] }

theorem u1767 : Upper (D 0) (R 0) [112,20,160,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1767
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1768 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 392 80 43 75 139 267), lower := (rows 113 22 164 392 80 32 64 128 256), losses := [] }

theorem u1768 : Upper (D 0) (R 0) [112,20,160,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1768
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1769 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 113 22 261 137 18 232 232 232 488), lower := (rows 113 22 261 137 18 32 64 128 256), losses := [] }

theorem u1769 : Upper (D 0) (R 0) [112,20,257,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1769
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1770 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 22 261 137 24 226 226 226 482), lower := (rows 113 22 261 137 24 32 64 128 256), losses := [] }

theorem u1770 : Upper (D 0) (R 0) [112,20,257,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1770
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1771 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 261 137 48 234 202 202 458), lower := (rows 113 22 261 137 48 32 64 128 256), losses := [] }

theorem u1771 : Upper (D 0) (R 0) [112,20,257,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1771
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1772 : Route 9 := (fun mask => (mask,id))

def c1772 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1772 : Upper (D 0) (R 0) [112,20,257,129,128] 13 := by
  apply FastRouting.sound _ _ [112,20,257,129,128] 13 (by decide) (choices 1) [2,8,64] r1772 c1772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u604
  · exact u605
  · exact u606

def b1773 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 261 138 17 232 232 232 488), lower := (rows 113 22 261 138 17 32 64 128 256), losses := [] }

theorem u1773 : Upper (D 0) (R 0) [112,20,257,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1773
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1774 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 22 261 138 24 225 225 225 481), lower := (rows 113 22 261 138 24 32 64 128 256), losses := [] }

theorem u1774 : Upper (D 0) (R 0) [112,20,257,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1774
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1775 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 261 138 48 233 201 201 457), lower := (rows 113 22 261 138 48 32 64 128 256), losses := [] }

theorem u1775 : Upper (D 0) (R 0) [112,20,257,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1775
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1776 : Route 9 := (fun mask => (mask,id))

def c1776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1776 : Upper (D 0) (R 0) [112,20,257,130,128] 13 := by
  apply FastRouting.sound _ _ [112,20,257,130,128] 13 (by decide) (choices 1) [1,8,64] r1776 c1776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u607
  · exact u608
  · exact u609

def b1777 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 261 168 17 234 202 202 458), lower := (rows 113 22 261 168 17 32 64 128 256), losses := [] }

theorem u1777 : Upper (D 0) (R 0) [112,20,257,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1777
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1778 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 113 22 261 168 18 233 201 201 457), lower := (rows 113 22 261 168 18 32 64 128 256), losses := [] }

theorem u1778 : Upper (D 0) (R 0) [112,20,257,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1778
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1779 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 261 168 24 227 195 195 451), lower := (rows 113 22 261 168 24 32 64 128 256), losses := [] }

theorem u1779 : Upper (D 0) (R 0) [112,20,257,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1779
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1780 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 261 168 80 171 203 139 395), lower := (rows 113 22 261 168 80 32 64 128 256), losses := [] }

theorem u1780 : Upper (D 0) (R 0) [112,20,257,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1780
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1781 : Route 9 := (fun mask => (mask,id))

def c1781 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1781 : Upper (D 0) (R 0) [112,20,257,160,128] 13 := by
  apply FastRouting.sound _ _ [112,20,257,160,128] 13 (by decide) (choices 1) [1,2,8,64] r1781 c1781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u610
  · exact u611
  · exact u612
  · exact u613

def b1782 : PairBound 9 := { available := 226, camps := [], pairs := [(1,5)], upper := (rows 113 22 268 137 17 226 226 226 482), lower := (rows 113 22 268 137 17 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 25 0 64 128 256), good := (rows 81 22 286 153 17 0 64 128 256) }] }

theorem u1782 : Upper (D 0) (R 0) [112,20,264,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1782
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1783 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 22 268 137 18 225 225 225 481), lower := (rows 113 22 268 137 18 32 64 128 256), losses := [] }

theorem u1783 : Upper (D 0) (R 0) [112,20,264,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1783
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1784 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 268 137 48 227 195 195 451), lower := (rows 113 22 268 137 48 32 64 128 256), losses := [] }

theorem u1784 : Upper (D 0) (R 0) [112,20,264,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1784
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1785 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 268 137 144 99 99 227 355), lower := (rows 113 22 268 137 144 32 64 128 256), losses := [] }

theorem u1785 : Upper (D 0) (R 0) [112,20,264,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1785
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1786 : PairBound 9 := { available := 225, camps := [], pairs := [(2,4)], upper := (rows 113 22 268 138 17 225 225 225 481), lower := (rows 113 22 268 138 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 6 10 0 49 81 145 273), good := (rows 481 494 268 142 481 32 64 128 256) }] }

theorem u1786 : Upper (D 0) (R 0) [112,20,264,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1786
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1787 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 268 138 48 225 193 193 449), lower := (rows 113 22 268 138 48 32 64 128 256), losses := [] }

theorem u1787 : Upper (D 0) (R 0) [112,20,264,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1787
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1788 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 268 138 144 97 97 225 353), lower := (rows 113 22 268 138 144 32 64 128 256), losses := [] }

theorem u1788 : Upper (D 0) (R 0) [112,20,264,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1788
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1789 : Route 9 := (fun mask => (mask,id))

def c1789 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1789 : Upper (D 0) (R 0) [112,20,264,160,1] 13 := by
  apply FastRouting.sound _ _ [112,20,264,160,1] 13 (by decide) (choices 1) [1,2,64,128] r1789 c1789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u614
  · exact u615
  · exact u616
  · exact u617

def b1790 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 268 168 18 225 193 193 449), lower := (rows 113 22 268 168 18 32 64 128 256), losses := [] }

theorem u1790 : Upper (D 0) (R 0) [112,20,264,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1790
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1791 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 268 168 80 163 195 131 387), lower := (rows 113 22 268 168 80 32 64 128 256), losses := [] }

theorem u1791 : Upper (D 0) (R 0) [112,20,264,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1791
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1792 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 268 168 144 99 67 195 323), lower := (rows 113 22 268 168 144 32 64 128 256), losses := [] }

theorem u1792 : Upper (D 0) (R 0) [112,20,264,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1792
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1793 : Route 9 := (fun mask => (mask,id))

def c1793 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1793 : Upper (D 0) (R 0) [112,20,288,129,1] 13 := by
  apply FastRouting.sound _ _ [112,20,288,129,1] 13 (by decide) (choices 1) [2,8,64,128] r1793 c1793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u618
  · exact u619
  · exact u620
  · exact u621

def b1794 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 113 22 292 137 18 233 201 201 457), lower := (rows 113 22 292 137 18 32 64 128 256), losses := [] }

theorem u1794 : Upper (D 0) (R 0) [112,20,288,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1794
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1795 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 292 137 24 227 195 195 451), lower := (rows 113 22 292 137 24 32 64 128 256), losses := [] }

theorem u1795 : Upper (D 0) (R 0) [112,20,288,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1795
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1796 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 292 137 80 171 203 139 395), lower := (rows 113 22 292 137 80 32 64 128 256), losses := [] }

theorem u1796 : Upper (D 0) (R 0) [112,20,288,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1796
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1797 : Route 9 := (fun mask => (mask,id))

def c1797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1797 : Upper (D 0) (R 0) [112,20,288,129,128] 13 := by
  apply FastRouting.sound _ _ [112,20,288,129,128] 13 (by decide) (choices 1) [1,2,8,64] r1797 c1797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u622
  · exact u623
  · exact u624
  · exact u625

def r1798 : Route 9 := (fun mask => (mask,id))

def c1798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1798 : Upper (D 0) (R 0) [112,20,288,130,1] 13 := by
  apply FastRouting.sound _ _ [112,20,288,130,1] 13 (by decide) (choices 1) [1,8,64,128] r1798 c1798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u626
  · exact u627
  · exact u628
  · exact u629

def b1799 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 292 138 24 225 193 193 449), lower := (rows 113 22 292 138 24 32 64 128 256), losses := [] }

theorem u1799 : Upper (D 0) (R 0) [112,20,288,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1799
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1799
end Delivery.IrregularNine14.P00
