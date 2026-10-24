import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0002
import IrregularNine14P05C0003

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r1860 : Route 9 := (fun mask => (mask,id))

def c1860 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1860 : Upper (D 5) (R 5) [6,17,72,33,160,256] 13 := by
  apply FastRouting.sound _ _ [6,17,72,33,160,256] 13 (by decide) (choices 1) [2,4,8] r1860 c1860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u133
  · exact u134
  · exact u135

def b1861 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 41 400 34 108 172 300), lower := (rows 7 19 76 41 400 34 64 128 256), losses := [] }

theorem u1861 : Upper (D 5) (R 5) [6,17,72,33,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1861
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1862 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 402, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 19 76 41 400 36 106 170 298), lower := (rows 7 19 76 41 400 36 64 128 256), losses := [] }

theorem u1862 : Upper (D 5) (R 5) [6,17,72,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1862
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1863 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 19 76 41 400 40 102 166 294), lower := (rows 7 19 76 41 400 40 64 128 256), losses := [] }

theorem u1863 : Upper (D 5) (R 5) [6,17,72,33,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1863
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1864 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 42 152 33 356 420 292), lower := (rows 7 19 76 42 152 33 64 128 256), losses := [] }

theorem u1864 : Upper (D 5) (R 5) [6,17,72,34,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1864
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1865 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(2,1),(3,0)], upper := (rows 7 19 76 42 152 36 353 417 289), lower := (rows 7 19 76 42 152 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 61 67 131 259), good := (rows 485 497 124 508 188 36 64 128 256) }] }

theorem u1865 : Upper (D 5) (R 5) [6,17,72,34,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1865
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1866 : Route 9 := (fun mask => (mask,id))

def c1866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1866 : Upper (D 5) (R 5) [6,17,72,34,136,256] 13 := by
  apply FastRouting.sound _ _ [6,17,72,34,136,256] 13 (by decide) (choices 1) [1,4,32] r1866 c1866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u136
  · exact u137
  · exact u138

def b1867 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 42 400 33 108 172 300), lower := (rows 7 19 76 42 400 33 64 128 256), losses := [] }

theorem u1867 : Upper (D 5) (R 5) [6,17,72,34,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1867
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1868 : Route 9 := (fun mask => (mask,id))

def c1868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1868 : Upper (D 5) (R 5) [6,17,72,34,384,4] 13 := by
  apply FastRouting.sound _ _ [6,17,72,34,384,4] 13 (by decide) (choices 1) [1,8,32] r1868 c1868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u139
  · exact u140
  · exact u141

def b1869 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 19 76 42 400 40 101 165 293), lower := (rows 7 19 76 42 400 40 64 128 256), losses := [] }

theorem u1869 : Upper (D 5) (R 5) [6,17,72,34,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1869
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1870 : Route 9 := (fun mask => (mask,id))

def c1870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1870 : Upper (D 5) (R 5) [6,17,72,36,136,1] 13 := by
  apply FastRouting.sound _ _ [6,17,72,36,136,1] 13 (by decide) (choices 1) [2,32,256] r1870 c1870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u142
  · exact u143
  · exact u144

def r1871 : Route 9 := (fun mask => (mask,id))

def c1871 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1871 : Upper (D 5) (R 5) [6,17,72,36,136,2] 13 := by
  apply FastRouting.sound _ _ [6,17,72,36,136,2] 13 (by decide) (choices 1) [1,32,256] r1871 c1871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u145
  · exact u146
  · exact u147

def r1872 : Route 9 := (fun mask => (mask,id))

def c1872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1872 : Upper (D 5) (R 5) [6,17,72,36,136,256] 13 := by
  apply FastRouting.sound _ _ [6,17,72,36,136,256] 13 (by decide) (choices 1) [1,2,32] r1872 c1872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u148
  · exact u149
  · exact u150

def r1873 : Route 9 := (fun mask => (mask,id))

def c1873 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1873 : Upper (D 5) (R 5) [6,17,72,36,160,1] 13 := by
  apply FastRouting.sound _ _ [6,17,72,36,160,1] 13 (by decide) (choices 1) [2,8,256] r1873 c1873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u151
  · exact u152
  · exact u153

def b1874 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(2,1),(3,0)], upper := (rows 7 19 76 44 176 34 329 393 265), lower := (rows 7 19 76 44 176 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 38 56 48 32 66 130 258), good := (rows 453 477 76 60 188 508 64 128 256) }] }

theorem u1874 : Upper (D 5) (R 5) [6,17,72,36,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1874
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1875 : PairBound 9 := { available := 259, camps := [{ cop := 6, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 44 176 40 323 387 259), lower := (rows 7 19 76 44 176 40 64 128 256), losses := [] }

theorem u1875 : Upper (D 5) (R 5) [6,17,72,36,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1875
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1876 : Route 9 := (fun mask => (mask,id))

def c1876 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1876 : Upper (D 5) (R 5) [6,17,72,36,160,256] 13 := by
  apply FastRouting.sound _ _ [6,17,72,36,160,256] 13 (by decide) (choices 1) [1,2,8] r1876 c1876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u154
  · exact u155
  · exact u156

def r1877 : Route 9 := (fun mask => (mask,id))

def c1877 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1877 : Upper (D 5) (R 5) [6,17,72,36,384,1] 13 := by
  apply FastRouting.sound _ _ [6,17,72,36,384,1] 13 (by decide) (choices 1) [2,8,32] r1877 c1877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u157
  · exact u158
  · exact u159

def r1878 : Route 9 := (fun mask => (mask,id))

def c1878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1878 : Upper (D 5) (R 5) [6,17,72,36,384,2] 13 := by
  apply FastRouting.sound _ _ [6,17,72,36,384,2] 13 (by decide) (choices 1) [1,8,32] r1878 c1878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u160
  · exact u161
  · exact u162

def b1879 : PairBound 9 := { available := 35, camps := [{ cop := 6, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 44 400 40 99 163 291), lower := (rows 7 19 76 44 400 40 64 128 256), losses := [] }

theorem u1879 : Upper (D 5) (R 5) [6,17,72,36,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1879
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1880 : PairBound 9 := { available := 44, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 19 76 137 304 34 108 172 300), lower := (rows 7 19 76 137 304 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 35 72 136 264), good := (rows 38 50 476 508 304 34 64 128 256) }] }

theorem u1880 : Upper (D 5) (R 5) [6,17,72,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1880
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1881 : Route 9 := (fun mask => (mask,id))

def c1881 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1881 : Upper (D 5) (R 5) [6,17,72,129,288,4] 13 := by
  apply FastRouting.sound _ _ [6,17,72,129,288,4] 13 (by decide) (choices 1) [2,8,32] r1881 c1881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u163
  · exact u164
  · exact u165

def b1882 : PairBound 9 := { available := 38, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 19 76 137 304 40 102 166 294), lower := (rows 7 19 76 137 304 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 25 44 65 129 257), good := (rows 502 466 124 508 304 60 64 128 256) }] }

theorem u1882 : Upper (D 5) (R 5) [6,17,72,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1882
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1883 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 324, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 138 56 33 356 420 292), lower := (rows 7 19 76 138 56 33 64 128 256), losses := [] }

theorem u1883 : Upper (D 5) (R 5) [6,17,72,130,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1883
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1884 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 76 138 56 36 353 417 289), lower := (rows 7 19 76 138 56 36 64 128 256), losses := [] }

theorem u1884 : Upper (D 5) (R 5) [6,17,72,130,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1884
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1885 : PairBound 9 := { available := 37, camps := [], pairs := [(4,1)], upper := (rows 7 19 76 138 56 288 101 165 293), lower := (rows 7 19 76 138 56 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 291 65 129 257), good := (rows 485 497 92 184 56 288 64 128 288) }] }

theorem u1885 : Upper (D 5) (R 5) [6,17,72,130,40,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1885
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1886 : PairBound 9 := { available := 36, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 19 76 138 280 33 100 164 292), lower := (rows 7 19 76 138 280 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 28 8 28 35 75 139 267), good := (rows 501 501 476 508 476 481 64 128 256) }] }

theorem u1886 : Upper (D 5) (R 5) [6,17,72,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1886
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1887 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 19 76 138 280 36 97 161 289), lower := (rows 7 19 76 138 280 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 61 67 131 259), good := (rows 485 497 124 508 316 36 64 128 256) }] }

theorem u1887 : Upper (D 5) (R 5) [6,17,72,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1887
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1888 : PairBound 9 := { available := 44, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 19 76 138 304 33 108 172 300), lower := (rows 7 19 76 138 304 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 35 72 136 264), good := (rows 37 49 476 508 304 33 64 128 256) }] }

theorem u1888 : Upper (D 5) (R 5) [6,17,72,130,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1888
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1889 : Route 9 := (fun mask => (mask,id))

def c1889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1889 : Upper (D 5) (R 5) [6,17,72,130,288,4] 13 := by
  apply FastRouting.sound _ _ [6,17,72,130,288,4] 13 (by decide) (choices 1) [1,8,32] r1889 c1889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u166
  · exact u167
  · exact u168

def r1890 : Route 9 := (fun mask => (mask,id))

def c1890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1890 : Upper (D 5) (R 5) [6,17,72,130,288,8] 13 := by
  apply FastRouting.sound _ _ [6,17,72,130,288,8] 13 (by decide) (choices 1) [1,4,32] r1890 c1890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u169
  · exact u170
  · exact u171

def r1891 : Route 9 := (fun mask => (mask,id))

def c1891 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1891 : Upper (D 5) (R 5) [6,17,72,132,40,1] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,40,1] 13 (by decide) (choices 1) [2,32,256] r1891 c1891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u172
  · exact u173
  · exact u174

def r1892 : Route 9 := (fun mask => (mask,id))

def c1892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1892 : Upper (D 5) (R 5) [6,17,72,132,40,2] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,40,2] 13 (by decide) (choices 1) [1,32,256] r1892 c1892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u175
  · exact u176
  · exact u177

def r1893 : Route 9 := (fun mask => (mask,id))

def c1893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1893 : Upper (D 5) (R 5) [6,17,72,132,40,256] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,40,256] 13 (by decide) (choices 1) [1,2,32] r1893 c1893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u178
  · exact u179
  · exact u180

def r1894 : Route 9 := (fun mask => (mask,id))

def c1894 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1894 : Upper (D 5) (R 5) [6,17,72,132,264,1] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,264,1] 13 (by decide) (choices 1) [2,32] r1894 c1894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u181
  · exact u182

def r1895 : Route 9 := (fun mask => (mask,id))

def c1895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1895 : Upper (D 5) (R 5) [6,17,72,132,264,2] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,264,2] 13 (by decide) (choices 1) [1,32] r1895 c1895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u183
  · exact u184

def r1896 : Route 9 := (fun mask => (mask,id))

def c1896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1896 : Upper (D 5) (R 5) [6,17,72,132,288,1] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,288,1] 13 (by decide) (choices 1) [2,8,32] r1896 c1896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u185
  · exact u186
  · exact u187

def r1897 : Route 9 := (fun mask => (mask,id))

def c1897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1897 : Upper (D 5) (R 5) [6,17,72,132,288,2] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,288,2] 13 (by decide) (choices 1) [1,8,32] r1897 c1897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u188
  · exact u189
  · exact u190

def b1898 : PairBound 9 := { available := 35, camps := [], pairs := [(1,2),(4,2)], upper := (rows 7 19 76 140 304 40 99 163 291), lower := (rows 7 19 76 140 304 40 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 17 44 65 129 257), good := (rows 499 467 104 168 304 40 64 128 256) }] }

theorem u1898 : Upper (D 5) (R 5) [6,17,72,132,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1898
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1899 : Route 9 := (fun mask => (mask,id))

def c1899 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1899 : Upper (D 5) (R 5) [6,17,72,160,264,1] 13 := by
  apply FastRouting.sound _ _ [6,17,72,160,264,1] 13 (by decide) (choices 1) [2,4,32] r1899 c1899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u191
  · exact u192
  · exact u193

def r1900 : Route 9 := (fun mask => (mask,id))

def c1900 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1900 : Upper (D 5) (R 5) [6,17,72,160,264,2] 13 := by
  apply FastRouting.sound _ _ [6,17,72,160,264,2] 13 (by decide) (choices 1) [1,4,32] r1900 c1900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u194
  · exact u195
  · exact u196

def r1901 : Route 9 := (fun mask => (mask,id))

def c1901 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1901 : Upper (D 5) (R 5) [6,17,72,160,264,4] 13 := by
  apply FastRouting.sound _ _ [6,17,72,160,264,4] 13 (by decide) (choices 1) [1,2,32] r1901 c1901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u197
  · exact u198
  · exact u199

def r1902 : Route 9 := (fun mask => (mask,id))

def c1902 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1902 : Upper (D 5) (R 5) [6,17,72,160,288,1] 13 := by
  apply FastRouting.sound _ _ [6,17,72,160,288,1] 13 (by decide) (choices 1) [2,4,8] r1902 c1902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u200
  · exact u201
  · exact u202

def r1903 : Route 9 := (fun mask => (mask,id))

def c1903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1903 : Upper (D 5) (R 5) [6,17,72,160,288,2] 13 := by
  apply FastRouting.sound _ _ [6,17,72,160,288,2] 13 (by decide) (choices 1) [1,4,8] r1903 c1903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u203
  · exact u204
  · exact u205

def r1904 : Route 9 := (fun mask => (mask,id))

def c1904 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1904 : Upper (D 5) (R 5) [6,17,72,160,288,4] 13 := by
  apply FastRouting.sound _ _ [6,17,72,160,288,4] 13 (by decide) (choices 1) [1,2,8] r1904 c1904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u206
  · exact u207
  · exact u208

def b1905 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 19 76 168 304 40 71 135 263), lower := (rows 7 19 76 168 304 40 64 128 256), losses := [] }

theorem u1905 : Upper (D 5) (R 5) [6,17,72,160,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1905
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1906 : Route 9 := (fun mask => (mask,id))

def c1906 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1906 : Upper (D 5) (R 5) [6,17,72,384,40,1] 13 := by
  apply FastRouting.sound _ _ [6,17,72,384,40,1] 13 (by decide) (choices 1) [2,4,32] r1906 c1906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u209
  · exact u210
  · exact u211

def r1907 : Route 9 := (fun mask => (mask,id))

def c1907 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1907 : Upper (D 5) (R 5) [6,17,72,384,40,2] 13 := by
  apply FastRouting.sound _ _ [6,17,72,384,40,2] 13 (by decide) (choices 1) [1,4,32] r1907 c1907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u212
  · exact u213
  · exact u214

def b1908 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 76 392 56 36 99 163 291), lower := (rows 7 19 76 392 56 36 64 128 256), losses := [] }

theorem u1908 : Upper (D 5) (R 5) [6,17,72,384,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1908
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1909 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 41 152 34 332 396 268), lower := (rows 7 19 100 41 152 34 64 128 256), losses := [] }

theorem u1909 : Upper (D 5) (R 5) [6,17,96,33,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1909
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1910 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 402, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 19 100 41 152 36 330 394 266), lower := (rows 7 19 100 41 152 36 64 128 256), losses := [] }

theorem u1910 : Upper (D 5) (R 5) [6,17,96,33,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1910
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1911 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 19 100 41 152 40 326 390 262), lower := (rows 7 19 100 41 152 40 64 128 256), losses := [] }

theorem u1911 : Upper (D 5) (R 5) [6,17,96,33,136,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1911
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1912 : Route 9 := (fun mask => (mask,id))

def c1912 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1912 : Upper (D 5) (R 5) [6,17,96,33,136,256] 13 := by
  apply FastRouting.sound _ _ [6,17,96,33,136,256] 13 (by decide) (choices 1) [2,4,8] r1912 c1912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u215
  · exact u216
  · exact u217

def b1913 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 41 400 34 76 140 268), lower := (rows 7 19 100 41 400 34 64 128 256), losses := [] }

theorem u1913 : Upper (D 5) (R 5) [6,17,96,33,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1913
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1914 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 402, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 19 100 41 400 36 74 138 266), lower := (rows 7 19 100 41 400 36 64 128 256), losses := [] }

theorem u1914 : Upper (D 5) (R 5) [6,17,96,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1914
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1915 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 19 100 41 400 40 78 142 270), lower := (rows 7 19 100 41 400 40 64 128 256), losses := [] }

theorem u1915 : Upper (D 5) (R 5) [6,17,96,33,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1915
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1916 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 42 152 33 332 396 268), lower := (rows 7 19 100 42 152 33 64 128 256), losses := [] }

theorem u1916 : Upper (D 5) (R 5) [6,17,96,34,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1916
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1917 : PairBound 9 := { available := 265, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 42 152 36 329 393 265), lower := (rows 7 19 100 42 152 36 64 128 256), losses := [] }

theorem u1917 : Upper (D 5) (R 5) [6,17,96,34,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1917
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1918 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 19 100 42 152 40 325 389 261), lower := (rows 7 19 100 42 152 40 64 128 256), losses := [] }

theorem u1918 : Upper (D 5) (R 5) [6,17,96,34,136,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1918
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1919 : Route 9 := (fun mask => (mask,id))

def c1919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1919 : Upper (D 5) (R 5) [6,17,96,34,136,256] 13 := by
  apply FastRouting.sound _ _ [6,17,96,34,136,256] 13 (by decide) (choices 1) [1,4,8] r1919 c1919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u218
  · exact u219
  · exact u220

#print axioms u1919
end Delivery.IrregularNine14.P05
