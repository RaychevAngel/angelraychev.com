import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0003
import IrregularNine14P01C0004

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1800 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 70 152 80 34 225 161 417), lower := (rows 305 14 70 152 80 34 64 128 256), losses := [] }

theorem u1800 : Upper (D 1) (R 1) [304,12,66,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1800
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1801 : Route 9 := (fun mask => (mask,id))

def c1801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1801 : Upper (D 1) (R 1) [304,12,66,144,64,128] 13 := by
  apply FastRouting.sound _ _ [304,12,66,144,64,128] 13 (by decide) (choices 1) [1,2,32] r1801 c1801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u229
  · exact u230
  · exact u231

def b1802 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 14 84 168 17 34 194 194 450), lower := (rows 305 14 84 168 17 34 64 128 256), losses := [] }

theorem u1802 : Upper (D 1) (R 1) [304,12,80,160,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1802
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1803 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 14 84 168 17 96 194 130 386), lower := (rows 305 14 84 168 17 96 64 128 256), losses := [] }

theorem u1803 : Upper (D 1) (R 1) [304,12,80,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1803
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1804 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 305 14 84 168 18 34 193 193 449), lower := (rows 305 14 84 168 18 34 64 128 256), losses := [] }

theorem u1804 : Upper (D 1) (R 1) [304,12,80,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1804
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1805 : Route 9 := (fun mask => (mask,id))

def c1805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1805 : Upper (D 1) (R 1) [304,12,80,160,2,64] 13 := by
  apply FastRouting.sound _ _ [304,12,80,160,2,64] 13 (by decide) (choices 1) [1,2,128] r1805 c1805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u232
  · exact u233
  · exact u234

def b1806 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 305 14 84 168 18 160 67 195 323), lower := (rows 305 14 84 168 18 160 64 128 256), losses := [] }

theorem u1806 : Upper (D 1) (R 1) [304,12,80,160,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1806
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1807 : Route 9 := (fun mask => (mask,id))

def c1807 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1807 : Upper (D 1) (R 1) [304,12,80,160,128,64] 13 := by
  apply FastRouting.sound _ _ [304,12,80,160,128,64] 13 (by decide) (choices 1) [1,2] r1807 c1807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u235
  · exact u236

def b1808 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 305 22 14 73 144 34 224 224 480), lower := (rows 305 22 14 73 144 34 64 128 256), losses := [] }

theorem u1808 : Upper (D 1) (R 1) [304,20,10,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1808
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1809 : Route 9 := (fun mask => (mask,id))

def c1809 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1809 : Upper (D 1) (R 1) [304,20,10,65,128,64] 13 := by
  apply FastRouting.sound _ _ [304,20,10,65,128,64] 13 (by decide) (choices 1) [2,32,128] r1809 c1809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u237
  · exact u238
  · exact u239

def b1810 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 14 73 144 160 98 226 354), lower := (rows 305 22 14 73 144 160 64 128 256), losses := [] }

theorem u1810 : Upper (D 1) (R 1) [304,20,10,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1810
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1811 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 22 14 104 144 33 194 194 450), lower := (rows 305 22 14 104 144 33 64 128 256), losses := [] }

theorem u1811 : Upper (D 1) (R 1) [304,20,10,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1811
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1812 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 305 22 14 104 144 34 193 193 449), lower := (rows 305 22 14 104 144 34 64 128 256), losses := [] }

theorem u1812 : Upper (D 1) (R 1) [304,20,10,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1812
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1813 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 14 104 144 96 195 131 387), lower := (rows 305 22 14 104 144 96 64 128 256), losses := [] }

theorem u1813 : Upper (D 1) (R 1) [304,20,10,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1813
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1814 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 14 104 144 160 67 195 323), lower := (rows 305 22 14 104 144 160 64 128 256), losses := [] }

theorem u1814 : Upper (D 1) (R 1) [304,20,10,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1814
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1815 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 22 44 74 144 33 194 194 450), lower := (rows 305 22 44 74 144 33 64 128 256), losses := [] }

theorem u1815 : Upper (D 1) (R 1) [304,20,40,66,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1815
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1816 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 22 44 74 144 34 193 193 449), lower := (rows 305 22 44 74 144 34 64 128 256), losses := [] }

theorem u1816 : Upper (D 1) (R 1) [304,20,40,66,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1816
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1817 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 305 22 44 74 144 96 195 131 387), lower := (rows 305 22 44 74 144 96 64 128 256), losses := [] }

theorem u1817 : Upper (D 1) (R 1) [304,20,40,66,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1817
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1818 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 44 74 144 160 67 195 323), lower := (rows 305 22 44 74 144 160 64 128 256), losses := [] }

theorem u1818 : Upper (D 1) (R 1) [304,20,40,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1818
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1819 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 305 22 70 73 144 34 232 168 424), lower := (rows 305 22 70 73 144 34 64 128 256), losses := [] }

theorem u1819 : Upper (D 1) (R 1) [304,20,66,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1819
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1820 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 22 70 73 144 40 226 162 418), lower := (rows 305 22 70 73 144 40 64 128 256), losses := [] }

theorem u1820 : Upper (D 1) (R 1) [304,20,66,65,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1820
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1821 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 70 73 144 160 106 170 298), lower := (rows 305 22 70 73 144 160 64 128 256), losses := [] }

theorem u1821 : Upper (D 1) (R 1) [304,20,66,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1821
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1822 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 22 70 104 144 33 202 138 394), lower := (rows 305 22 70 104 144 33 64 128 256), losses := [] }

theorem u1822 : Upper (D 1) (R 1) [304,20,66,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1822
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1823 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 70 104 144 34 201 137 393), lower := (rows 305 22 70 104 144 34 64 128 256), losses := [] }

theorem u1823 : Upper (D 1) (R 1) [304,20,66,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1823
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1824 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 70 104 144 40 195 131 387), lower := (rows 305 22 70 104 144 40 64 128 256), losses := [] }

theorem u1824 : Upper (D 1) (R 1) [304,20,66,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1824
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1825 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 70 104 144 160 75 139 267), lower := (rows 305 22 70 104 144 160 64 128 256), losses := [] }

theorem u1825 : Upper (D 1) (R 1) [304,20,66,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1825
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1826 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 305 22 70 137 144 34 104 232 360), lower := (rows 305 22 70 137 144 34 64 128 256), losses := [] }

theorem u1826 : Upper (D 1) (R 1) [304,20,66,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1826
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1827 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 305 22 70 137 144 40 98 226 354), lower := (rows 305 22 70 137 144 40 64 128 256), losses := [] }

theorem u1827 : Upper (D 1) (R 1) [304,20,66,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1827
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1828 : Route 9 := (fun mask => (mask,id))

def c1828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1828 : Upper (D 1) (R 1) [304,20,66,129,128,64] 13 := by
  apply FastRouting.sound _ _ [304,20,66,129,128,64] 13 (by decide) (choices 1) [2,8,32] r1828 c1828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u240
  · exact u241
  · exact u242

def b1829 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 305 22 70 168 144 33 74 202 330), lower := (rows 305 22 70 168 144 33 64 128 256), losses := [] }

theorem u1829 : Upper (D 1) (R 1) [304,20,66,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1829
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1830 : PairBound 9 := { available := 73, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 305 22 70 168 144 34 73 201 329), lower := (rows 305 22 70 168 144 34 64 128 256), losses := [] }

theorem u1830 : Upper (D 1) (R 1) [304,20,66,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1830
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1831 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 22 70 168 144 40 67 195 323), lower := (rows 305 22 70 168 144 40 64 128 256), losses := [] }

theorem u1831 : Upper (D 1) (R 1) [304,20,66,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1831
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1832 : Route 9 := (fun mask => (mask,id))

def c1832 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1832 : Upper (D 1) (R 1) [304,20,66,160,128,64] 13 := by
  apply FastRouting.sound _ _ [304,20,66,160,128,64] 13 (by decide) (choices 1) [1,2,8] r1832 c1832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u243
  · exact u244
  · exact u245

def b1833 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 22 76 42 144 33 194 194 450), lower := (rows 305 22 76 42 144 33 64 128 256), losses := [] }

theorem u1833 : Upper (D 1) (R 1) [304,20,72,34,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1833
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1834 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 76 42 144 34 193 193 449), lower := (rows 305 22 76 42 144 34 64 128 256), losses := [] }

theorem u1834 : Upper (D 1) (R 1) [304,20,72,34,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1834
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1835 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 76 42 144 96 195 131 387), lower := (rows 305 22 76 42 144 96 64 128 256), losses := [] }

theorem u1835 : Upper (D 1) (R 1) [304,20,72,34,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1835
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1836 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 76 42 144 160 67 195 323), lower := (rows 305 22 76 42 144 160 64 128 256), losses := [] }

theorem u1836 : Upper (D 1) (R 1) [304,20,72,34,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1836
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1837 : Route 9 := (fun mask => (mask,id))

def c1837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1837 : Upper (D 1) (R 1) [304,20,96,65,128,2] 13 := by
  apply FastRouting.sound _ _ [304,20,96,65,128,2] 13 (by decide) (choices 1) [2,8,128] r1837 c1837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u246
  · exact u247
  · exact u248

def b1838 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 22 100 73 144 40 194 130 386), lower := (rows 305 22 100 73 144 40 64 128 256), losses := [] }

theorem u1838 : Upper (D 1) (R 1) [304,20,96,65,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1838
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1839 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 100 73 144 160 74 138 266), lower := (rows 305 22 100 73 144 160 64 128 256), losses := [] }

theorem u1839 : Upper (D 1) (R 1) [304,20,96,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1839
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1840 : Route 9 := (fun mask => (mask,id))

def c1840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1840 : Upper (D 1) (R 1) [304,20,96,129,128,2] 13 := by
  apply FastRouting.sound _ _ [304,20,96,129,128,2] 13 (by decide) (choices 1) [2,8] r1840 c1840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u249
  · exact u250

def b1841 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 305 22 100 137 144 40 66 194 322), lower := (rows 305 22 100 137 144 40 64 128 256), losses := [] }

theorem u1841 : Upper (D 1) (R 1) [304,20,96,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1841
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1842 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 100 137 144 96 74 138 266), lower := (rows 305 22 100 137 144 96 64 128 256), losses := [] }

theorem u1842 : Upper (D 1) (R 1) [304,20,96,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1842
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1843 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 305 22 100 138 144 33 74 202 330), lower := (rows 305 22 100 138 144 33 64 128 256), losses := [] }

theorem u1843 : Upper (D 1) (R 1) [304,20,96,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1843
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1844 : Route 9 := (fun mask => (mask,id))

def c1844 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1844 : Upper (D 1) (R 1) [304,20,96,130,128,2] 13 := by
  apply FastRouting.sound _ _ [304,20,96,130,128,2] 13 (by decide) (choices 1) [1,8] r1844 c1844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u251
  · exact u252

def b1845 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 22 100 138 144 40 67 195 323), lower := (rows 305 22 100 138 144 40 64 128 256), losses := [] }

theorem u1845 : Upper (D 1) (R 1) [304,20,96,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1845
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1846 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 100 138 144 96 75 139 267), lower := (rows 305 22 100 138 144 96 64 128 256), losses := [] }

theorem u1846 : Upper (D 1) (R 1) [304,20,96,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1846
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1847 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 22 100 200 144 33 74 138 266), lower := (rows 305 22 100 200 144 33 64 128 256), losses := [] }

theorem u1847 : Upper (D 1) (R 1) [304,20,96,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1847
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1848 : Route 9 := (fun mask => (mask,id))

def c1848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1848 : Upper (D 1) (R 1) [304,20,96,192,128,2] 13 := by
  apply FastRouting.sound _ _ [304,20,96,192,128,2] 13 (by decide) (choices 1) [1,2,8] r1848 c1848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u253
  · exact u254
  · exact u255

def b1849 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 22 100 200 144 40 67 131 259), lower := (rows 305 22 100 200 144 40 64 128 256), losses := [] }

theorem u1849 : Upper (D 1) (R 1) [304,20,96,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1849
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1850 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 67 14 140 18 96 240 176 432), lower := (rows 305 67 14 140 18 96 64 128 256), losses := [] }

theorem u1850 : Upper (D 1) (R 1) [304,65,10,132,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1850
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1851 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 14 140 48 96 210 146 402), lower := (rows 305 67 14 140 48 96 64 128 256), losses := [] }

theorem u1851 : Upper (D 1) (R 1) [304,65,10,132,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1851
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1852 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 305 67 14 140 80 160 114 178 306), lower := (rows 305 67 14 140 80 160 64 128 256), losses := [] }

theorem u1852 : Upper (D 1) (R 1) [304,65,10,132,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1852
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1853 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 305 67 14 152 18 36 224 224 480), lower := (rows 305 67 14 152 18 36 64 128 256), losses := [] }

theorem u1853 : Upper (D 1) (R 1) [304,65,10,144,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1853
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1854 : PairBound 9 := { available := 164, camps := [], pairs := [(2,6)], upper := (rows 305 67 14 152 18 96 228 164 420), lower := (rows 305 67 14 152 18 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 22 11 22 32 0 129 257), good := (rows 445 415 30 156 30 32 0 128 256) }] }

theorem u1854 : Upper (D 1) (R 1) [304,65,10,144,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1854
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1855 : Route 9 := (fun mask => (mask,id))

def c1855 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1855 : Upper (D 1) (R 1) [304,65,10,144,2,128] 13 := by
  apply FastRouting.sound _ _ [304,65,10,144,2,128] 13 (by decide) (choices 1) [4,32] r1855 c1855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u256
  · exact u257

def b1856 : PairBound 9 := { available := 164, camps := [], pairs := [(2,6)], upper := (rows 305 67 14 152 80 34 228 164 420), lower := (rows 305 67 14 152 80 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 6 9 16 38 0 166 294), good := (rows 441 431 430 152 16 422 0 128 256) }] }

theorem u1856 : Upper (D 1) (R 1) [304,65,10,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1856
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1857 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 67 14 152 80 36 226 162 418), lower := (rows 305 67 14 152 80 36 64 128 256), losses := [] }

theorem u1857 : Upper (D 1) (R 1) [304,65,10,144,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1857
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1858 : Route 9 := (fun mask => (mask,id))

def c1858 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1858 : Upper (D 1) (R 1) [304,65,10,144,64,128] 13 := by
  apply FastRouting.sound _ _ [304,65,10,144,64,128] 13 (by decide) (choices 1) [2,4,32] r1858 c1858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u258
  · exact u259
  · exact u260

def b1859 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 28 104 18 34 196 132 388), lower := (rows 305 67 28 104 18 34 64 128 256), losses := [] }

theorem u1859 : Upper (D 1) (R 1) [304,65,24,96,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1859
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1859
end Delivery.IrregularNine14.P01
