import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0004
import IrregularNine14P03C0005

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1860 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 259 7 44 73 145 48 224 224 480), lower := (rows 259 7 44 73 145 48 64 128 256), losses := [] }

theorem u1860 : Upper (D 3) (R 3) [258,5,40,65,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1860
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1861 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 44 73 145 96 240 176 432), lower := (rows 259 7 44 73 145 96 64 128 256), losses := [] }

theorem u1861 : Upper (D 3) (R 3) [258,5,40,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1861
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1862 : Route 9 := (fun mask => (mask,id))

def c1862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1862 : Upper (D 3) (R 3) [258,5,40,65,129,128] 13 := by
  apply FastRouting.sound _ _ [258,5,40,65,129,128] 13 (by decide) (choices 1) [16,32] r1862 c1862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u295
  · exact u296

def b1863 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 259 7 44 73 176 33 208 208 464), lower := (rows 259 7 44 73 176 33 64 128 256), losses := [] }

theorem u1863 : Upper (D 3) (R 3) [258,5,40,65,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1863
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1864 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 7 44 73 176 48 193 193 449), lower := (rows 259 7 44 73 176 48 64 128 256), losses := [] }

theorem u1864 : Upper (D 3) (R 3) [258,5,40,65,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1864
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1865 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 44 73 176 96 209 145 401), lower := (rows 259 7 44 73 176 96 64 128 256), losses := [] }

theorem u1865 : Upper (D 3) (R 3) [258,5,40,65,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1865
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1866 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 44 73 176 160 81 209 337), lower := (rows 259 7 44 73 176 160 64 128 256), losses := [] }

theorem u1866 : Upper (D 3) (R 3) [258,5,40,65,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1866
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1867 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 259 7 44 73 208 33 240 176 432), lower := (rows 259 7 44 73 208 33 64 128 256), losses := [] }

theorem u1867 : Upper (D 3) (R 3) [258,5,40,65,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1867
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1868 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 7 44 73 208 48 225 161 417), lower := (rows 259 7 44 73 208 48 64 128 256), losses := [] }

theorem u1868 : Upper (D 3) (R 3) [258,5,40,65,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1868
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1869 : Route 9 := (fun mask => (mask,id))

def c1869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1869 : Upper (D 3) (R 3) [258,5,40,65,192,128] 13 := by
  apply FastRouting.sound _ _ [258,5,40,65,192,128] 13 (by decide) (choices 1) [1,16,32] r1869 c1869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u297
  · exact u298
  · exact u299

def b1870 : PairBound 9 := { available := 224, camps := [], pairs := [(2,6)], upper := (rows 259 7 44 88 145 33 224 224 480), lower := (rows 259 7 44 88 145 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 51 0 128 256), good := (rows 291 39 44 60 177 33 0 128 256) }] }

theorem u1870 : Upper (D 3) (R 3) [258,5,40,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1870
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1871 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 44 88 145 96 225 161 417), lower := (rows 259 7 44 88 145 96 64 128 256), losses := [] }

theorem u1871 : Upper (D 3) (R 3) [258,5,40,80,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1871
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1872 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 44 88 145 160 97 225 353), lower := (rows 259 7 44 88 145 160 64 128 256), losses := [] }

theorem u1872 : Upper (D 3) (R 3) [258,5,40,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1872
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1873 : Route 9 := (fun mask => (mask,id))

def c1873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1873 : Upper (D 3) (R 3) [258,5,40,192,65,1] 13 := by
  apply FastRouting.sound _ _ [258,5,40,192,65,1] 13 (by decide) (choices 1) [16,32,128] r1873 c1873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u300
  · exact u301
  · exact u302

def b1874 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 7 44 200 81 48 225 161 417), lower := (rows 259 7 44 200 81 48 64 128 256), losses := [] }

theorem u1874 : Upper (D 3) (R 3) [258,5,40,192,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1874
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1875 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 44 200 81 160 113 177 305), lower := (rows 259 7 44 200 81 160 64 128 256), losses := [] }

theorem u1875 : Upper (D 3) (R 3) [258,5,40,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1875
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1876 : Route 9 := (fun mask => (mask,id))

def c1876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1876 : Upper (D 3) (R 3) [258,5,40,192,96,1] 13 := by
  apply FastRouting.sound _ _ [258,5,40,192,96,1] 13 (by decide) (choices 1) [1,16,128] r1876 c1876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u303
  · exact u304
  · exact u305

def b1877 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 7 44 200 112 48 193 129 385), lower := (rows 259 7 44 200 112 48 64 128 256), losses := [] }

theorem u1877 : Upper (D 3) (R 3) [258,5,40,192,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1877
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1878 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 44 200 112 160 81 145 273), lower := (rows 259 7 44 200 112 160 64 128 256), losses := [] }

theorem u1878 : Upper (D 3) (R 3) [258,5,40,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1878
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1879 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 25 152 33 224 224 480), lower := (rows 259 7 100 25 152 33 64 128 256), losses := [] }

theorem u1879 : Upper (D 3) (R 3) [258,5,96,17,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1879
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1880 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 100 25 152 96 225 161 417), lower := (rows 259 7 100 25 152 96 64 128 256), losses := [] }

theorem u1880 : Upper (D 3) (R 3) [258,5,96,17,136,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1880
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1881 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 25 152 160 97 225 353), lower := (rows 259 7 100 25 152 160 64 128 256), losses := [] }

theorem u1881 : Upper (D 3) (R 3) [258,5,96,17,136,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1881
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1882 : Route 9 := (fun mask => (mask,id))

def c1882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1882 : Upper (D 3) (R 3) [258,5,96,17,160,1] 13 := by
  apply FastRouting.sound _ _ [258,5,96,17,160,1] 13 (by decide) (choices 1) [8,128] r1882 c1882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u306
  · exact u307

def b1883 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 7 100 25 176 40 193 193 449), lower := (rows 259 7 100 25 176 40 64 128 256), losses := [] }

theorem u1883 : Upper (D 3) (R 3) [258,5,96,17,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1883
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1884 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 100 25 176 96 201 137 393), lower := (rows 259 7 100 25 176 96 64 128 256), losses := [] }

theorem u1884 : Upper (D 3) (R 3) [258,5,96,17,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1884
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1885 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 25 176 160 73 201 329), lower := (rows 259 7 100 25 176 160 64 128 256), losses := [] }

theorem u1885 : Upper (D 3) (R 3) [258,5,96,17,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1885
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1886 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 259 7 100 56 145 33 200 200 456), lower := (rows 259 7 100 56 145 33 64 128 256), losses := [] }

theorem u1886 : Upper (D 3) (R 3) [258,5,96,48,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1886
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1887 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 7 100 56 145 40 193 193 449), lower := (rows 259 7 100 56 145 40 64 128 256), losses := [] }

theorem u1887 : Upper (D 3) (R 3) [258,5,96,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1887
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1888 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 100 56 145 96 201 137 393), lower := (rows 259 7 100 56 145 96 64 128 256), losses := [] }

theorem u1888 : Upper (D 3) (R 3) [258,5,96,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1888
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1889 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 56 145 160 73 201 329), lower := (rows 259 7 100 56 145 160 64 128 256), losses := [] }

theorem u1889 : Upper (D 3) (R 3) [258,5,96,48,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1889
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1890 : Route 9 := (fun mask => (mask,id))

def c1890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1890 : Upper (D 3) (R 3) [258,5,96,48,192,1] 13 := by
  apply FastRouting.sound _ _ [258,5,96,48,192,1] 13 (by decide) (choices 1) [1,8,128] r1890 c1890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u308
  · exact u309
  · exact u310

def b1891 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 7 100 56 208 40 193 129 385), lower := (rows 259 7 100 56 208 40 64 128 256), losses := [] }

theorem u1891 : Upper (D 3) (R 3) [258,5,96,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1891
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1892 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 56 208 160 73 137 265), lower := (rows 259 7 100 56 208 160 64 128 256), losses := [] }

theorem u1892 : Upper (D 3) (R 3) [258,5,96,48,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1892
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1893 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 259 7 100 137 176 33 88 216 344), lower := (rows 259 7 100 137 176 33 64 128 256), losses := [] }

theorem u1893 : Upper (D 3) (R 3) [258,5,96,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1893
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1894 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 259 7 100 137 176 40 81 209 337), lower := (rows 259 7 100 137 176 40 64 128 256), losses := [] }

theorem u1894 : Upper (D 3) (R 3) [258,5,96,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1894
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1895 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 259 7 100 137 176 48 73 201 329), lower := (rows 259 7 100 137 176 48 64 128 256), losses := [] }

theorem u1895 : Upper (D 3) (R 3) [258,5,96,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1895
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1896 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 100 137 176 96 89 153 281), lower := (rows 259 7 100 137 176 96 64 128 256), losses := [] }

theorem u1896 : Upper (D 3) (R 3) [258,5,96,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1896
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1897 : Route 9 := (fun mask => (mask,id))

def c1897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1897 : Upper (D 3) (R 3) [258,5,96,160,192,1] 13 := by
  apply FastRouting.sound _ _ [258,5,96,160,192,1] 13 (by decide) (choices 1) [1,8,16] r1897 c1897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u311
  · exact u312
  · exact u313

def b1898 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 7 100 168 208 40 81 145 273), lower := (rows 259 7 100 168 208 40 64 128 256), losses := [] }

theorem u1898 : Upper (D 3) (R 3) [258,5,96,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1898
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1899 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 259 7 100 168 208 48 73 137 265), lower := (rows 259 7 100 168 208 48 64 128 256), losses := [] }

theorem u1899 : Upper (D 3) (R 3) [258,5,96,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1899
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1900 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 259 14 21 41 208 33 224 224 480), lower := (rows 259 14 21 41 208 33 64 128 256), losses := [] }

theorem u1900 : Upper (D 3) (R 3) [258,12,17,33,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1900
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1901 : PairBound 9 := { available := 161, camps := [], pairs := [(0,6)], upper := (rows 259 14 21 41 208 96 225 161 417), lower := (rows 259 14 21 41 208 96 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 32 0 136 264), good := (rows 259 399 21 425 144 32 0 128 256) }] }

theorem u1901 : Upper (D 3) (R 3) [258,12,17,33,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1901
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1902 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 38, targets := 128 }], pairs := [(1,7)], upper := (rows 259 14 37 73 112 33 208 144 400), lower := (rows 259 14 37 73 112 33 64 128 256), losses := [] }

theorem u1902 : Upper (D 3) (R 3) [258,12,33,65,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1902
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1903 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 14 37 73 112 48 193 129 385), lower := (rows 259 14 37 73 112 48 64 128 256), losses := [] }

theorem u1903 : Upper (D 3) (R 3) [258,12,33,65,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1903
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m1904_1 : Upper (D 3) (R 3) [258,12,33,65,96,128,1] 13 :=
  permutation_upper _ _ _ [258,12,33,65,96,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u314

theorem m1904_16 : Upper (D 3) (R 3) [258,12,33,65,96,128,16] 13 :=
  permutation_upper _ _ _ [258,12,33,65,96,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u315

def r1904 : Route 9 := (fun mask => (mask,id))

def c1904 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1904 : Upper (D 3) (R 3) [258,12,33,65,96,128] 13 := by
  apply FastRouting.sound _ _ [258,12,33,65,96,128] 13 (by decide) (choices 1) [1,16,128] r1904 c1904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1904_1
  · exact m1904_16
  · exact u316

def b1905 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 259 14 37 73 145 48 224 224 480), lower := (rows 259 14 37 73 145 48 64 128 256), losses := [] }

theorem u1905 : Upper (D 3) (R 3) [258,12,33,65,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1905
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1906 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 38, targets := 128 }], pairs := [(1,7)], upper := (rows 259 14 37 73 145 96 240 176 432), lower := (rows 259 14 37 73 145 96 64 128 256), losses := [] }

theorem u1906 : Upper (D 3) (R 3) [258,12,33,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1906
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1907 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 259 14 37 73 145 160 112 240 368), lower := (rows 259 14 37 73 145 160 64 128 256), losses := [] }

theorem u1907 : Upper (D 3) (R 3) [258,12,33,65,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1907
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1908 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 259 14 37 73 176 33 208 208 464), lower := (rows 259 14 37 73 176 33 64 128 256), losses := [] }

theorem u1908 : Upper (D 3) (R 3) [258,12,33,65,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1908
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1909 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 14 37 73 176 48 193 193 449), lower := (rows 259 14 37 73 176 48 64 128 256), losses := [] }

theorem u1909 : Upper (D 3) (R 3) [258,12,33,65,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1909
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1910 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 38, targets := 128 }], pairs := [(1,7)], upper := (rows 259 14 37 73 176 96 209 145 401), lower := (rows 259 14 37 73 176 96 64 128 256), losses := [] }

theorem u1910 : Upper (D 3) (R 3) [258,12,33,65,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1910
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1911 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 37 73 176 160 81 209 337), lower := (rows 259 14 37 73 176 160 64 128 256), losses := [] }

theorem u1911 : Upper (D 3) (R 3) [258,12,33,65,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1911
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1912 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 259 14 37 88 145 33 224 224 480), lower := (rows 259 14 37 88 145 33 64 128 256), losses := [] }

theorem u1912 : Upper (D 3) (R 3) [258,12,33,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1912
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1913 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 259 14 37 88 145 96 225 161 417), lower := (rows 259 14 37 88 145 96 64 128 256), losses := [] }

theorem u1913 : Upper (D 3) (R 3) [258,12,33,80,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1913
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1914 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 259 14 37 88 145 160 97 225 353), lower := (rows 259 14 37 88 145 160 64 128 256), losses := [] }

theorem u1914 : Upper (D 3) (R 3) [258,12,33,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1914
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1915 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 259 14 37 200 112 33 209 145 401), lower := (rows 259 14 37 200 112 33 64 128 256), losses := [] }

theorem u1915 : Upper (D 3) (R 3) [258,12,33,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1915
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1916 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 14 37 200 112 48 193 129 385), lower := (rows 259 14 37 200 112 48 64 128 256), losses := [] }

theorem u1916 : Upper (D 3) (R 3) [258,12,33,192,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1916
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1917 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 259 14 37 200 112 160 81 145 273), lower := (rows 259 14 37 200 112 160 64 128 256), losses := [] }

theorem u1917 : Upper (D 3) (R 3) [258,12,33,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1917
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1918 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 28 208 33 224 224 480), lower := (rows 259 35 13 28 208 33 64 128 256), losses := [] }

theorem u1918 : Upper (D 3) (R 3) [258,33,9,20,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1918
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1919 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 28 208 96 225 161 417), lower := (rows 259 35 13 28 208 96 64 128 256), losses := [] }

theorem u1919 : Upper (D 3) (R 3) [258,33,9,20,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1919
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1919
end Delivery.IrregularNine14.P03
