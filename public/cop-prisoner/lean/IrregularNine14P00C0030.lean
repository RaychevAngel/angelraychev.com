import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0010
import IrregularNine14P00C0011

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1800 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 292 138 80 169 201 137 393), lower := (rows 113 22 292 138 80 32 64 128 256), losses := [] }

theorem u1800 : Upper (D 0) (R 0) [112,20,288,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1800
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1801 : Route 9 := (fun mask => (mask,id))

def c1801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1801 : Upper (D 0) (R 0) [112,20,288,130,128] 13 := by
  apply FastRouting.sound _ _ [112,20,288,130,128] 13 (by decide) (choices 1) [1,8,64] r1801 c1801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u630
  · exact u631
  · exact u632

def r1802 : Route 9 := (fun mask => (mask,id))

def c1802 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1802 : Upper (D 0) (R 0) [112,20,288,192,1] 13 := by
  apply FastRouting.sound _ _ [112,20,288,192,1] 13 (by decide) (choices 1) [1,2,8,128] r1802 c1802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u633
  · exact u634
  · exact u635
  · exact u636

def b1803 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 113 22 292 200 18 169 201 137 393), lower := (rows 113 22 292 200 18 32 64 128 256), losses := [] }

theorem u1803 : Upper (D 0) (R 0) [112,20,288,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1803
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1804 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 22 292 200 24 163 195 131 387), lower := (rows 113 22 292 200 24 32 64 128 256), losses := [] }

theorem u1804 : Upper (D 0) (R 0) [112,20,288,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1804
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1805 : Route 9 := (fun mask => (mask,id))

def c1805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1805 : Upper (D 0) (R 0) [112,20,288,192,128] 13 := by
  apply FastRouting.sound _ _ [112,20,288,192,128] 13 (by decide) (choices 1) [1,2,8] r1805 c1805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u637
  · exact u638
  · exact u639

def r1806 : Route 9 := (fun mask => (mask,id))

def c1806 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1806 : Upper (D 0) (R 0) [112,20,384,129,1] 13 := by
  apply FastRouting.sound _ _ [112,20,384,129,1] 13 (by decide) (choices 1) [2,8,64] r1806 c1806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u640
  · exact u641
  · exact u642

def b1807 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 113 22 388 137 18 105 105 233 361), lower := (rows 113 22 388 137 18 32 64 128 256), losses := [] }

theorem u1807 : Upper (D 0) (R 0) [112,20,384,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1807
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1808 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 22 388 137 24 99 99 227 355), lower := (rows 113 22 388 137 24 32 64 128 256), losses := [] }

theorem u1808 : Upper (D 0) (R 0) [112,20,384,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1808
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1809 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 388 137 48 107 75 203 331), lower := (rows 113 22 388 137 48 32 64 128 256), losses := [] }

theorem u1809 : Upper (D 0) (R 0) [112,20,384,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1809
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1810 : Route 9 := (fun mask => (mask,id))

def c1810 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1810 : Upper (D 0) (R 0) [112,20,384,160,1] 13 := by
  apply FastRouting.sound _ _ [112,20,384,160,1] 13 (by decide) (choices 1) [1,2,8,64] r1810 c1810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u643
  · exact u644
  · exact u645
  · exact u646

def b1811 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 113 22 388 168 18 105 73 201 329), lower := (rows 113 22 388 168 18 32 64 128 256), losses := [] }

theorem u1811 : Upper (D 0) (R 0) [112,20,384,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1811
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1812 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 22 388 168 24 99 67 195 323), lower := (rows 113 22 388 168 24 32 64 128 256), losses := [] }

theorem u1812 : Upper (D 0) (R 0) [112,20,384,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1812
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1813 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 388 168 80 43 75 139 267), lower := (rows 113 22 388 168 80 32 64 128 256), losses := [] }

theorem u1813 : Upper (D 0) (R 0) [112,20,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1813
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1814 : PairBound 9 := { available := 116, camps := [], pairs := [], upper := (rows 113 131 140 265 18 116 116 244 372), lower := (rows 113 131 140 265 18 32 64 128 256), losses := [] }

theorem u1814 : Upper (D 0) (R 0) [112,129,136,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1814
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1815 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 113 131 140 265 20 114 114 242 370), lower := (rows 113 131 140 265 20 32 64 128 256), losses := [] }

theorem u1815 : Upper (D 0) (R 0) [112,129,136,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1815
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1816 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 140 265 48 118 86 214 342), lower := (rows 113 131 140 265 48 32 64 128 256), losses := [] }

theorem u1816 : Upper (D 0) (R 0) [112,129,136,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1816
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1817 : Route 9 := (fun mask => (mask,id))

def c1817 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1817 : Upper (D 0) (R 0) [112,129,136,272,1] 13 := by
  apply FastRouting.sound _ _ [112,129,136,272,1] 13 (by decide) (choices 1) [2,4,64] r1817 c1817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u647
  · exact u648
  · exact u649

def b1818 : PairBound 9 := { available := 101, camps := [], pairs := [], upper := (rows 113 131 140 280 18 101 101 229 357), lower := (rows 113 131 140 280 18 32 64 128 256), losses := [] }

theorem u1818 : Upper (D 0) (R 0) [112,129,136,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1818
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1819 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 131 140 280 20 99 99 227 355), lower := (rows 113 131 140 280 20 32 64 128 256), losses := [] }

theorem u1819 : Upper (D 0) (R 0) [112,129,136,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1819
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1820 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 140 280 48 103 71 199 327), lower := (rows 113 131 140 280 48 32 64 128 256), losses := [] }

theorem u1820 : Upper (D 0) (R 0) [112,129,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1820
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1821 : PairBound 9 := { available := 108, camps := [], pairs := [], upper := (rows 113 131 148 265 18 108 108 236 364), lower := (rows 113 131 148 265 18 32 64 128 256), losses := [] }

theorem u1821 : Upper (D 0) (R 0) [112,129,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1821
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1822 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 131 148 265 20 106 106 234 362), lower := (rows 113 131 148 265 20 32 64 128 256), losses := [] }

theorem u1822 : Upper (D 0) (R 0) [112,129,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1822
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1823 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 113 131 148 265 24 102 102 230 358), lower := (rows 113 131 148 265 24 32 64 128 256), losses := [] }

theorem u1823 : Upper (D 0) (R 0) [112,129,144,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1823
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1824 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 148 265 48 110 78 206 334), lower := (rows 113 131 148 265 48 32 64 128 256), losses := [] }

theorem u1824 : Upper (D 0) (R 0) [112,129,144,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1824
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1825 : PairBound 9 := { available := 108, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 148 266 17 108 108 236 364), lower := (rows 113 131 148 266 17 32 64 128 256), losses := [] }

theorem u1825 : Upper (D 0) (R 0) [112,129,144,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1825
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1826 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 113 131 148 266 20 105 105 233 361), lower := (rows 113 131 148 266 20 32 64 128 256), losses := [] }

theorem u1826 : Upper (D 0) (R 0) [112,129,144,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1826
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1827 : PairBound 9 := { available := 101, camps := [], pairs := [], upper := (rows 113 131 148 266 24 101 101 229 357), lower := (rows 113 131 148 266 24 32 64 128 256), losses := [] }

theorem u1827 : Upper (D 0) (R 0) [112,129,144,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1827
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1828 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 148 266 48 109 77 205 333), lower := (rows 113 131 148 266 48 32 64 128 256), losses := [] }

theorem u1828 : Upper (D 0) (R 0) [112,129,144,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1828
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1829 : PairBound 9 := { available := 106, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 148 268 17 106 106 234 362), lower := (rows 113 131 148 268 17 32 64 128 256), losses := [] }

theorem u1829 : Upper (D 0) (R 0) [112,129,144,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1829
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1830 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 113 131 148 268 18 105 105 233 361), lower := (rows 113 131 148 268 18 32 64 128 256), losses := [] }

theorem u1830 : Upper (D 0) (R 0) [112,129,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1830
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1831 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 131 148 268 24 99 99 227 355), lower := (rows 113 131 148 268 24 32 64 128 256), losses := [] }

theorem u1831 : Upper (D 0) (R 0) [112,129,144,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1831
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1832 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 148 268 48 107 75 203 331), lower := (rows 113 131 148 268 48 32 64 128 256), losses := [] }

theorem u1832 : Upper (D 0) (R 0) [112,129,144,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1832
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1833 : PairBound 9 := { available := 78, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 148 296 17 110 78 206 334), lower := (rows 113 131 148 296 17 32 64 128 256), losses := [] }

theorem u1833 : Upper (D 0) (R 0) [112,129,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1833
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1834 : PairBound 9 := { available := 77, camps := [], pairs := [], upper := (rows 113 131 148 296 18 109 77 205 333), lower := (rows 113 131 148 296 18 32 64 128 256), losses := [] }

theorem u1834 : Upper (D 0) (R 0) [112,129,144,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1834
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1835 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 113 131 148 296 20 107 75 203 331), lower := (rows 113 131 148 296 20 32 64 128 256), losses := [] }

theorem u1835 : Upper (D 0) (R 0) [112,129,144,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1835
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1836 : PairBound 9 := { available := 71, camps := [], pairs := [], upper := (rows 113 131 148 296 24 103 71 199 327), lower := (rows 113 131 148 296 24 32 64 128 256), losses := [] }

theorem u1836 : Upper (D 0) (R 0) [112,129,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1836
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1837 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 148 296 80 47 79 143 271), lower := (rows 113 131 148 296 80 32 64 128 256), losses := [] }

theorem u1837 : Upper (D 0) (R 0) [112,129,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1837
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1838 : PairBound 9 := { available := 106, camps := [], pairs := [(3,5)], upper := (rows 113 134 261 152 17 106 106 234 362), lower := (rows 113 134 261 152 17 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 21 0 64 128 256), good := (rows 81 158 277 152 17 0 64 128 256) }] }

theorem u1838 : Upper (D 0) (R 0) [112,132,257,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1838
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1839 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 113 134 261 152 18 105 105 233 361), lower := (rows 113 134 261 152 18 32 64 128 256), losses := [] }

theorem u1839 : Upper (D 0) (R 0) [112,132,257,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1839
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1840 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 134 261 152 24 99 99 227 355), lower := (rows 113 134 261 152 24 32 64 128 256), losses := [] }

theorem u1840 : Upper (D 0) (R 0) [112,132,257,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1840
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1841 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 261 152 48 107 75 203 331), lower := (rows 113 134 261 152 48 32 64 128 256), losses := [] }

theorem u1841 : Upper (D 0) (R 0) [112,132,257,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1841
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1842 : Route 9 := (fun mask => (mask,id))

def c1842 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1842 : Upper (D 0) (R 0) [112,132,272,160,1] 13 := by
  apply FastRouting.sound _ _ [112,132,272,160,1] 13 (by decide) (choices 1) [1,2,8,64] r1842 c1842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u650
  · exact u651
  · exact u652
  · exact u653

def b1843 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 113 134 276 168 18 105 73 201 329), lower := (rows 113 134 276 168 18 32 64 128 256), losses := [] }

theorem u1843 : Upper (D 0) (R 0) [112,132,272,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1843
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1844 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 134 276 168 24 99 67 195 323), lower := (rows 113 134 276 168 24 32 64 128 256), losses := [] }

theorem u1844 : Upper (D 0) (R 0) [112,132,272,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1844
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1845 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 276 168 80 43 75 139 267), lower := (rows 113 134 276 168 80 32 64 128 256), losses := [] }

theorem u1845 : Upper (D 0) (R 0) [112,132,272,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1845
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1846 : Route 9 := (fun mask => (mask,id))

def c1846 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1846 : Upper (D 0) (R 0) [112,144,160,257,1] 13 := by
  apply FastRouting.sound _ _ [112,144,160,257,1] 13 (by decide) (choices 1) [2,4,8,64] r1846 c1846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u654
  · exact u655
  · exact u656
  · exact u657

def b1847 : PairBound 9 := { available := 77, camps := [], pairs := [], upper := (rows 113 146 164 265 18 109 77 205 333), lower := (rows 113 146 164 265 18 32 64 128 256), losses := [] }

theorem u1847 : Upper (D 0) (R 0) [112,144,160,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1847
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1848 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 113 146 164 265 20 107 75 203 331), lower := (rows 113 146 164 265 20 32 64 128 256), losses := [] }

theorem u1848 : Upper (D 0) (R 0) [112,144,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1848
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1849 : PairBound 9 := { available := 71, camps := [], pairs := [], upper := (rows 113 146 164 265 24 103 71 199 327), lower := (rows 113 146 164 265 24 32 64 128 256), losses := [] }

theorem u1849 : Upper (D 0) (R 0) [112,144,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1849
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1850 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 164 265 80 47 79 143 271), lower := (rows 113 146 164 265 80 32 64 128 256), losses := [] }

theorem u1850 : Upper (D 0) (R 0) [112,144,160,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1850
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1851 : Route 9 := (fun mask => (mask,id))

def c1851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1851 : Upper (D 0) (R 0) [112,144,160,258,1] 13 := by
  apply FastRouting.sound _ _ [112,144,160,258,1] 13 (by decide) (choices 1) [1,4,8,64] r1851 c1851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u658
  · exact u659
  · exact u660
  · exact u661

def b1852 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 113 146 164 266 20 105 73 201 329), lower := (rows 113 146 164 266 20 32 64 128 256), losses := [] }

theorem u1852 : Upper (D 0) (R 0) [112,144,160,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1852
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1853 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 113 146 164 266 24 101 69 197 325), lower := (rows 113 146 164 266 24 32 64 128 256), losses := [] }

theorem u1853 : Upper (D 0) (R 0) [112,144,160,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1853
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1854 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 164 266 80 45 77 141 269), lower := (rows 113 146 164 266 80 32 64 128 256), losses := [] }

theorem u1854 : Upper (D 0) (R 0) [112,144,160,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1854
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1855 : Route 9 := (fun mask => (mask,id))

def c1855 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1855 : Upper (D 0) (R 0) [112,144,160,320,1] 13 := by
  apply FastRouting.sound _ _ [112,144,160,320,1] 13 (by decide) (choices 1) [1,2,4,8] r1855 c1855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u662
  · exact u663
  · exact u664
  · exact u665

def b1856 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 113 146 164 328 18 45 77 141 269), lower := (rows 113 146 164 328 18 32 64 128 256), losses := [] }

theorem u1856 : Upper (D 0) (R 0) [112,144,160,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1856
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1857 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 113 146 164 328 20 43 75 139 267), lower := (rows 113 146 164 328 20 32 64 128 256), losses := [] }

theorem u1857 : Upper (D 0) (R 0) [112,144,160,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1857
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1858 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 113 146 164 328 24 39 71 135 263), lower := (rows 113 146 164 328 24 32 64 128 256), losses := [] }

theorem u1858 : Upper (D 0) (R 0) [112,144,160,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1858
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1859 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 263 11 52 88 17 224 224 224 480), lower := (rows 263 11 52 88 17 32 64 128 256), losses := [] }

theorem u1859 : Upper (D 0) (R 0) [262,9,48,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1859
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1859
end Delivery.IrregularNine14.P00
