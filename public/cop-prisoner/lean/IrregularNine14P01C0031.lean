import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0004

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1860 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 67 28 104 18 36 194 130 386), lower := (rows 305 67 28 104 18 36 64 128 256), losses := [] }

theorem u1860 : Upper (D 1) (R 1) [304,65,24,96,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1860
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1861 : Route 9 := (fun mask => (mask,id))

def c1861 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1861 : Upper (D 1) (R 1) [304,65,24,96,2,128] 13 := by
  apply FastRouting.sound _ _ [304,65,24,96,2,128] 13 (by decide) (choices 1) [2,4,128] r1861 c1861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u261
  · exact u262
  · exact u263

def b1862 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 305 67 28 104 144 34 198 134 390), lower := (rows 305 67 28 104 144 34 64 128 256), losses := [] }

theorem u1862 : Upper (D 1) (R 1) [304,65,24,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1862
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1863 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 67 28 104 144 36 194 130 386), lower := (rows 305 67 28 104 144 36 64 128 256), losses := [] }

theorem u1863 : Upper (D 1) (R 1) [304,65,24,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1863
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1864 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 67 28 104 144 160 70 134 262), lower := (rows 305 67 28 104 144 160 64 128 256), losses := [] }

theorem u1864 : Upper (D 1) (R 1) [304,65,24,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1864
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1865 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 28 168 18 34 196 196 452), lower := (rows 305 67 28 168 18 34 64 128 256), losses := [] }

theorem u1865 : Upper (D 1) (R 1) [304,65,24,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1865
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1866 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 67 28 168 18 36 194 194 450), lower := (rows 305 67 28 168 18 36 64 128 256), losses := [] }

theorem u1866 : Upper (D 1) (R 1) [304,65,24,160,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1866
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1867 : PairBound 9 := { available := 134, camps := [], pairs := [(2,6)], upper := (rows 305 67 28 168 18 96 198 134 390), lower := (rows 305 67 28 168 18 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 7 9 18 32 0 146 274), good := (rows 445 415 412 168 406 32 0 128 256) }] }

theorem u1867 : Upper (D 1) (R 1) [304,65,24,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1867
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1868 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 305 67 28 168 18 160 70 198 326), lower := (rows 305 67 28 168 18 160 64 128 256), losses := [] }

theorem u1868 : Upper (D 1) (R 1) [304,65,24,160,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1868
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1869 : PairBound 9 := { available := 134, camps := [], pairs := [(2,6)], upper := (rows 305 67 28 168 80 34 198 134 390), lower := (rows 305 67 28 168 80 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 42 16 34 0 130 258), good := (rows 317 431 28 168 16 426 0 128 256) }] }

theorem u1869 : Upper (D 1) (R 1) [304,65,24,160,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1869
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1870 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 67 28 168 80 36 194 130 386), lower := (rows 305 67 28 168 80 36 64 128 256), losses := [] }

theorem u1870 : Upper (D 1) (R 1) [304,65,24,160,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1870
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1871 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 305 67 28 168 80 160 70 134 262), lower := (rows 305 67 28 168 80 160 64 128 256), losses := [] }

theorem u1871 : Upper (D 1) (R 1) [304,65,24,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1871
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1872 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 28 200 18 34 228 164 420), lower := (rows 305 67 28 200 18 34 64 128 256), losses := [] }

theorem u1872 : Upper (D 1) (R 1) [304,65,24,192,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1872
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1873 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 67 28 200 18 36 226 162 418), lower := (rows 305 67 28 200 18 36 64 128 256), losses := [] }

theorem u1873 : Upper (D 1) (R 1) [304,65,24,192,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1873
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1874 : Route 9 := (fun mask => (mask,id))

def c1874 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1874 : Upper (D 1) (R 1) [304,65,24,192,2,128] 13 := by
  apply FastRouting.sound _ _ [304,65,24,192,2,128] 13 (by decide) (choices 1) [2,4,32] r1874 c1874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u264
  · exact u265
  · exact u266

def b1875 : PairBound 9 := { available := 52, camps := [], pairs := [(0,6)], upper := (rows 305 67 76 138 18 160 116 180 308), lower := (rows 305 67 76 138 18 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 26 172 0 132 260), good := (rows 305 19 445 186 18 160 0 160 256) }] }

theorem u1875 : Upper (D 1) (R 1) [304,65,72,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1875
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1876 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 67 76 138 20 160 114 178 306), lower := (rows 305 67 76 138 20 160 64 128 256), losses := [] }

theorem u1876 : Upper (D 1) (R 1) [304,65,72,130,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1876
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1877 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 76 138 48 160 86 150 278), lower := (rows 305 67 76 138 48 160 64 128 256), losses := [] }

theorem u1877 : Upper (D 1) (R 1) [304,65,72,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1877
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1878 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 76 152 18 34 228 164 420), lower := (rows 305 67 76 152 18 34 64 128 256), losses := [] }

theorem u1878 : Upper (D 1) (R 1) [304,65,72,144,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1878
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1879 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 67 76 152 18 36 226 162 418), lower := (rows 305 67 76 152 18 36 64 128 256), losses := [] }

theorem u1879 : Upper (D 1) (R 1) [304,65,72,144,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1879
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1880 : Route 9 := (fun mask => (mask,id))

def c1880 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1880 : Upper (D 1) (R 1) [304,65,72,144,2,128] 13 := by
  apply FastRouting.sound _ _ [304,65,72,144,2,128] 13 (by decide) (choices 1) [2,4,32] r1880 c1880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u267
  · exact u268
  · exact u269

def r1881 : Route 9 := (fun mask => (mask,id))

def c1881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1881 : Upper (D 1) (R 1) [304,65,80,130,128,2] 13 := by
  apply FastRouting.sound _ _ [304,65,80,130,128,2] 13 (by decide) (choices 1) [4,8,32] r1881 c1881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u270
  · exact u271
  · exact u272

def b1882 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 305 67 84 138 144 36 106 170 298), lower := (rows 305 67 84 138 144 36 64 128 256), losses := [] }

theorem u1882 : Upper (D 1) (R 1) [304,65,80,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1882
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1883 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 305 67 84 138 144 40 102 166 294), lower := (rows 305 67 84 138 144 40 64 128 256), losses := [] }

theorem u1883 : Upper (D 1) (R 1) [304,65,80,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1883
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1884 : Route 9 := (fun mask => (mask,id))

def c1884 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1884 : Upper (D 1) (R 1) [304,65,80,132,128,2] 13 := by
  apply FastRouting.sound _ _ [304,65,80,132,128,2] 13 (by decide) (choices 1) [2,8,32] r1884 c1884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u273
  · exact u274
  · exact u275

def b1885 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 67 84 140 144 40 98 162 290), lower := (rows 305 67 84 140 144 40 64 128 256), losses := [] }

theorem u1885 : Upper (D 1) (R 1) [304,65,80,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1885
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1886 : Route 9 := (fun mask => (mask,id))

def c1886 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1886 : Upper (D 1) (R 1) [304,65,80,160,128,2] 13 := by
  apply FastRouting.sound _ _ [304,65,80,160,128,2] 13 (by decide) (choices 1) [2,4,8] r1886 c1886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u276
  · exact u277
  · exact u278

def b1887 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 67 84 168 144 36 74 138 266), lower := (rows 305 67 84 168 144 36 64 128 256), losses := [] }

theorem u1887 : Upper (D 1) (R 1) [304,65,80,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1887
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1888 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 305 67 84 168 144 40 70 134 262), lower := (rows 305 67 84 168 144 40 64 128 256), losses := [] }

theorem u1888 : Upper (D 1) (R 1) [304,65,80,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1888
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1889 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 305 67 134 200 18 36 120 184 312), lower := (rows 305 67 134 200 18 36 64 128 256), losses := [] }

theorem u1889 : Upper (D 1) (R 1) [304,65,130,192,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1889
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1890 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 305 67 134 200 18 40 116 180 308), lower := (rows 305 67 134 200 18 40 64 128 256), losses := [] }

theorem u1890 : Upper (D 1) (R 1) [304,65,130,192,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1890
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1891 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 206, targets := 16 }], pairs := [(1,4)], upper := (rows 305 67 134 200 18 48 108 172 300), lower := (rows 305 67 134 200 18 48 64 128 256), losses := [] }

theorem u1891 : Upper (D 1) (R 1) [304,65,130,192,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1891
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1892 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 148 168 18 34 76 204 332), lower := (rows 305 67 148 168 18 34 64 128 256), losses := [] }

theorem u1892 : Upper (D 1) (R 1) [304,65,144,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1892
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1893 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 305 67 148 168 18 36 74 202 330), lower := (rows 305 67 148 168 18 36 64 128 256), losses := [] }

theorem u1893 : Upper (D 1) (R 1) [304,65,144,160,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1893
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1894 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 305 67 148 168 18 40 70 198 326), lower := (rows 305 67 148 168 18 40 64 128 256), losses := [] }

theorem u1894 : Upper (D 1) (R 1) [304,65,144,160,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1894
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1895 : Route 9 := (fun mask => (mask,id))

def c1895 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1895 : Upper (D 1) (R 1) [304,65,144,160,2,64] 13 := by
  apply FastRouting.sound _ _ [304,65,144,160,2,64] 13 (by decide) (choices 1) [2,4,8] r1895 c1895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u279
  · exact u280
  · exact u281

def b1896 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 67 148 168 20 96 74 138 266), lower := (rows 305 67 148 168 20 96 64 128 256), losses := [] }

theorem u1896 : Upper (D 1) (R 1) [304,65,144,160,4,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1896
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1897 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 305 67 148 168 24 96 70 134 262), lower := (rows 305 67 148 168 24 96 64 128 256), losses := [] }

theorem u1897 : Upper (D 1) (R 1) [304,65,144,160,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1897
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1898 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 148 200 18 34 108 172 300), lower := (rows 305 67 148 200 18 34 64 128 256), losses := [] }

theorem u1898 : Upper (D 1) (R 1) [304,65,144,192,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1898
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1899 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 305 67 148 200 18 36 106 170 298), lower := (rows 305 67 148 200 18 36 64 128 256), losses := [] }

theorem u1899 : Upper (D 1) (R 1) [304,65,144,192,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1899
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1900 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 305 67 148 200 18 40 102 166 294), lower := (rows 305 67 148 200 18 40 64 128 256), losses := [] }

theorem u1900 : Upper (D 1) (R 1) [304,65,144,192,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1900
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1901 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 7 88 144 34 232 168 424), lower := (rows 305 70 7 88 144 34 64 128 256), losses := [] }

theorem u1901 : Upper (D 1) (R 1) [304,68,3,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1901
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1902 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 70 7 88 144 40 226 162 418), lower := (rows 305 70 7 88 144 40 64 128 256), losses := [] }

theorem u1902 : Upper (D 1) (R 1) [304,68,3,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1902
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1903 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 70 7 88 144 160 106 170 298), lower := (rows 305 70 7 88 144 160 64 128 256), losses := [] }

theorem u1903 : Upper (D 1) (R 1) [304,68,3,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1903
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1904 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 7 152 80 34 232 168 424), lower := (rows 305 70 7 152 80 34 64 128 256), losses := [] }

theorem u1904 : Upper (D 1) (R 1) [304,68,3,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1904
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1905 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 70 7 152 80 40 226 162 418), lower := (rows 305 70 7 152 80 40 64 128 256), losses := [] }

theorem u1905 : Upper (D 1) (R 1) [304,68,3,144,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1905
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1906 : Route 9 := (fun mask => (mask,id))

def c1906 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1906 : Upper (D 1) (R 1) [304,68,3,144,64,128] 13 := by
  apply FastRouting.sound _ _ [304,68,3,144,64,128] 13 (by decide) (choices 1) [2,8,32] r1906 c1906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u282
  · exact u283
  · exact u284

def b1907 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 7 200 18 160 120 184 312), lower := (rows 305 70 7 200 18 160 64 128 256), losses := [] }

theorem u1907 : Upper (D 1) (R 1) [304,68,3,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1907
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1908 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 70 7 200 24 160 114 178 306), lower := (rows 305 70 7 200 24 160 64 128 256), losses := [] }

theorem u1908 : Upper (D 1) (R 1) [304,68,3,192,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1908
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1909 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 7 200 48 160 90 154 282), lower := (rows 305 70 7 200 48 160 64 128 256), losses := [] }

theorem u1909 : Upper (D 1) (R 1) [304,68,3,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1909
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1910 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 13 138 18 96 240 176 432), lower := (rows 305 70 13 138 18 96 64 128 256), losses := [] }

theorem u1910 : Upper (D 1) (R 1) [304,68,9,130,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1910
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1911 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 13 138 18 160 112 240 368), lower := (rows 305 70 13 138 18 160 64 128 256), losses := [] }

theorem u1911 : Upper (D 1) (R 1) [304,68,9,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1911
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1912 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 13 138 48 96 210 146 402), lower := (rows 305 70 13 138 48 96 64 128 256), losses := [] }

theorem u1912 : Upper (D 1) (R 1) [304,68,9,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1912
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1913 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 13 138 48 160 82 210 338), lower := (rows 305 70 13 138 48 160 64 128 256), losses := [] }

theorem u1913 : Upper (D 1) (R 1) [304,68,9,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1913
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1914 : Route 9 := (fun mask => (mask,id))

def c1914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1914 : Upper (D 1) (R 1) [304,68,9,130,64,128] 13 := by
  apply FastRouting.sound _ _ [304,68,9,130,64,128] 13 (by decide) (choices 1) [2,16,32] r1914 c1914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u285
  · exact u286
  · exact u287

def b1915 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 14 137 18 96 240 176 432), lower := (rows 305 70 14 137 18 96 64 128 256), losses := [] }

theorem u1915 : Upper (D 1) (R 1) [304,68,10,129,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1915
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1916 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 14 137 18 160 112 240 368), lower := (rows 305 70 14 137 18 160 64 128 256), losses := [] }

theorem u1916 : Upper (D 1) (R 1) [304,68,10,129,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1916
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1917 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 14 137 48 96 210 146 402), lower := (rows 305 70 14 137 48 96 64 128 256), losses := [] }

theorem u1917 : Upper (D 1) (R 1) [304,68,10,129,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1917
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1918 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 14 137 48 160 82 210 338), lower := (rows 305 70 14 137 48 160 64 128 256), losses := [] }

theorem u1918 : Upper (D 1) (R 1) [304,68,10,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1918
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1919 : Route 9 := (fun mask => (mask,id))

def c1919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1919 : Upper (D 1) (R 1) [304,68,10,129,64,128] 13 := by
  apply FastRouting.sound _ _ [304,68,10,129,64,128] 13 (by decide) (choices 1) [2,16,32] r1919 c1919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u288
  · exact u289
  · exact u290

#print axioms u1919
end Delivery.IrregularNine14.P01
