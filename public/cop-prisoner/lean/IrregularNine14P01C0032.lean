import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0004
import IrregularNine14P01C0005

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1920 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 70 14 152 80 33 226 162 418), lower := (rows 305 70 14 152 80 33 64 128 256), losses := [] }

theorem u1920 : Upper (D 1) (R 1) [304,68,10,144,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1920
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1921 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 14 152 80 34 225 161 417), lower := (rows 305 70 14 152 80 34 64 128 256), losses := [] }

theorem u1921 : Upper (D 1) (R 1) [304,68,10,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1921
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1922 : Route 9 := (fun mask => (mask,id))

def c1922 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1922 : Upper (D 1) (R 1) [304,68,10,144,64,128] 13 := by
  apply FastRouting.sound _ _ [304,68,10,144,64,128] 13 (by decide) (choices 1) [1,2,32] r1922 c1922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u291
  · exact u292
  · exact u293

def b1923 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 22 73 144 34 232 168 424), lower := (rows 305 70 22 73 144 34 64 128 256), losses := [] }

theorem u1923 : Upper (D 1) (R 1) [304,68,18,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1923
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1924 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 70 22 73 144 40 226 162 418), lower := (rows 305 70 22 73 144 40 64 128 256), losses := [] }

theorem u1924 : Upper (D 1) (R 1) [304,68,18,65,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1924
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1925 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 70 22 73 144 160 106 170 298), lower := (rows 305 70 22 73 144 160 64 128 256), losses := [] }

theorem u1925 : Upper (D 1) (R 1) [304,68,18,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1925
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1926 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 70 22 104 144 33 202 138 394), lower := (rows 305 70 22 104 144 33 64 128 256), losses := [] }

theorem u1926 : Upper (D 1) (R 1) [304,68,18,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1926
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1927 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 22 104 144 34 201 137 393), lower := (rows 305 70 22 104 144 34 64 128 256), losses := [] }

theorem u1927 : Upper (D 1) (R 1) [304,68,18,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1927
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1928 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 70 22 104 144 40 195 131 387), lower := (rows 305 70 22 104 144 40 64 128 256), losses := [] }

theorem u1928 : Upper (D 1) (R 1) [304,68,18,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1928
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1929 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 70 22 104 144 160 75 139 267), lower := (rows 305 70 22 104 144 160 64 128 256), losses := [] }

theorem u1929 : Upper (D 1) (R 1) [304,68,18,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1929
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1930 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 22 137 144 34 104 232 360), lower := (rows 305 70 22 137 144 34 64 128 256), losses := [] }

theorem u1930 : Upper (D 1) (R 1) [304,68,18,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1930
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1931 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 305 70 22 137 144 40 98 226 354), lower := (rows 305 70 22 137 144 40 64 128 256), losses := [] }

theorem u1931 : Upper (D 1) (R 1) [304,68,18,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1931
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1932 : Route 9 := (fun mask => (mask,id))

def c1932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1932 : Upper (D 1) (R 1) [304,68,18,129,128,64] 13 := by
  apply FastRouting.sound _ _ [304,68,18,129,128,64] 13 (by decide) (choices 1) [2,8,32] r1932 c1932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u294
  · exact u295
  · exact u296

def b1933 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 305 70 22 168 144 33 74 202 330), lower := (rows 305 70 22 168 144 33 64 128 256), losses := [] }

theorem u1933 : Upper (D 1) (R 1) [304,68,18,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1933
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1934 : PairBound 9 := { available := 73, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 22 168 144 34 73 201 329), lower := (rows 305 70 22 168 144 34 64 128 256), losses := [] }

theorem u1934 : Upper (D 1) (R 1) [304,68,18,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1934
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1935 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 70 22 168 144 40 67 195 323), lower := (rows 305 70 22 168 144 40 64 128 256), losses := [] }

theorem u1935 : Upper (D 1) (R 1) [304,68,18,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1935
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1936 : Route 9 := (fun mask => (mask,id))

def c1936 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1936 : Upper (D 1) (R 1) [304,68,18,160,128,64] 13 := by
  apply FastRouting.sound _ _ [304,68,18,160,128,64] 13 (by decide) (choices 1) [1,2,8] r1936 c1936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u297
  · exact u298
  · exact u299

def b1937 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 70 28 42 144 33 194 194 450), lower := (rows 305 70 28 42 144 33 64 128 256), losses := [] }

theorem u1937 : Upper (D 1) (R 1) [304,68,24,34,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1937
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1938 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 28 42 144 34 193 193 449), lower := (rows 305 70 28 42 144 34 64 128 256), losses := [] }

theorem u1938 : Upper (D 1) (R 1) [304,68,24,34,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1938
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1939 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 28 42 144 96 195 131 387), lower := (rows 305 70 28 42 144 96 64 128 256), losses := [] }

theorem u1939 : Upper (D 1) (R 1) [304,68,24,34,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1939
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1940 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 70 28 42 144 160 67 195 323), lower := (rows 305 70 28 42 144 160 64 128 256), losses := [] }

theorem u1940 : Upper (D 1) (R 1) [304,68,24,34,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1940
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1941 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 70 28 168 18 33 194 194 450), lower := (rows 305 70 28 168 18 33 64 128 256), losses := [] }

theorem u1941 : Upper (D 1) (R 1) [304,68,24,160,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1941
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1942 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 28 168 18 34 193 193 449), lower := (rows 305 70 28 168 18 34 64 128 256), losses := [] }

theorem u1942 : Upper (D 1) (R 1) [304,68,24,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1942
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1943 : Route 9 := (fun mask => (mask,id))

def c1943 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1943 : Upper (D 1) (R 1) [304,68,24,160,2,64] 13 := by
  apply FastRouting.sound _ _ [304,68,24,160,2,64] 13 (by decide) (choices 1) [1,2,128] r1943 c1943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u300
  · exact u301
  · exact u302

def b1944 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 28 168 18 160 67 195 323), lower := (rows 305 70 28 168 18 160 64 128 256), losses := [] }

theorem u1944 : Upper (D 1) (R 1) [304,68,24,160,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1944
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1945 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 70 28 168 80 33 194 130 386), lower := (rows 305 70 28 168 80 33 64 128 256), losses := [] }

theorem u1945 : Upper (D 1) (R 1) [304,68,24,160,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1945
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1946 : Route 9 := (fun mask => (mask,id))

def c1946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1946 : Upper (D 1) (R 1) [304,68,24,160,64,2] 13 := by
  apply FastRouting.sound _ _ [304,68,24,160,64,2] 13 (by decide) (choices 1) [1,2,128] r1946 c1946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u303
  · exact u304
  · exact u305

def b1947 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 28 168 80 160 67 131 259), lower := (rows 305 70 28 168 80 160 64 128 256), losses := [] }

theorem u1947 : Upper (D 1) (R 1) [304,68,24,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1947
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1948 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 133 152 18 34 104 232 360), lower := (rows 305 70 133 152 18 34 64 128 256), losses := [] }

theorem u1948 : Upper (D 1) (R 1) [304,68,129,144,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1948
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1949 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 305 70 133 152 18 40 98 226 354), lower := (rows 305 70 133 152 18 40 64 128 256), losses := [] }

theorem u1949 : Upper (D 1) (R 1) [304,68,129,144,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1949
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1950 : Route 9 := (fun mask => (mask,id))

def c1950 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1950 : Upper (D 1) (R 1) [304,68,129,144,2,64] 13 := by
  apply FastRouting.sound _ _ [304,68,129,144,2,64] 13 (by decide) (choices 1) [2,8,32] r1950 c1950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u306
  · exact u307
  · exact u308

def r1951 : Route 9 := (fun mask => (mask,id))

def c1951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1951 : Upper (D 1) (R 1) [304,68,129,144,64,2] 13 := by
  apply FastRouting.sound _ _ [304,68,129,144,64,2] 13 (by decide) (choices 1) [2,8,32] r1951 c1951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u309
  · exact u310
  · exact u311

def b1952 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 70 133 152 80 40 98 162 290), lower := (rows 305 70 133 152 80 40 64 128 256), losses := [] }

theorem u1952 : Upper (D 1) (R 1) [304,68,129,144,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1952
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1953 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 133 200 18 34 120 184 312), lower := (rows 305 70 133 200 18 34 64 128 256), losses := [] }

theorem u1953 : Upper (D 1) (R 1) [304,68,129,192,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1953
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1954 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 70 133 200 18 40 114 178 306), lower := (rows 305 70 133 200 18 40 64 128 256), losses := [] }

theorem u1954 : Upper (D 1) (R 1) [304,68,129,192,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1954
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1955 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 206, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 133 200 18 48 106 170 298), lower := (rows 305 70 133 200 18 48 64 128 256), losses := [] }

theorem u1955 : Upper (D 1) (R 1) [304,68,129,192,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1955
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1956 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 134 73 18 160 120 184 312), lower := (rows 305 70 134 73 18 160 64 128 256), losses := [] }

theorem u1956 : Upper (D 1) (R 1) [304,68,130,65,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1956
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1957 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 70 134 73 24 160 114 178 306), lower := (rows 305 70 134 73 24 160 64 128 256), losses := [] }

theorem u1957 : Upper (D 1) (R 1) [304,68,130,65,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1957
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1958 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 134 73 48 160 90 154 282), lower := (rows 305 70 134 73 48 160 64 128 256), losses := [] }

theorem u1958 : Upper (D 1) (R 1) [304,68,130,65,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1958
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1959 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 134 137 18 96 120 184 312), lower := (rows 305 70 134 137 18 96 64 128 256), losses := [] }

theorem u1959 : Upper (D 1) (R 1) [304,68,130,129,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1959
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1960 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 70 134 137 24 96 114 178 306), lower := (rows 305 70 134 137 24 96 64 128 256), losses := [] }

theorem u1960 : Upper (D 1) (R 1) [304,68,130,129,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1960
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1961 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 134 137 48 96 90 154 282), lower := (rows 305 70 134 137 48 96 64 128 256), losses := [] }

theorem u1961 : Upper (D 1) (R 1) [304,68,130,129,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1961
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1962 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 140 11 18 96 240 176 432), lower := (rows 305 70 140 11 18 96 64 128 256), losses := [] }

theorem u1962 : Upper (D 1) (R 1) [304,68,136,3,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1962
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1963 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 140 11 18 160 112 240 368), lower := (rows 305 70 140 11 18 160 64 128 256), losses := [] }

theorem u1963 : Upper (D 1) (R 1) [304,68,136,3,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1963
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1964 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 140 11 48 96 210 146 402), lower := (rows 305 70 140 11 48 96 64 128 256), losses := [] }

theorem u1964 : Upper (D 1) (R 1) [304,68,136,3,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1964
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1965 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 140 11 48 160 82 210 338), lower := (rows 305 70 140 11 48 160 64 128 256), losses := [] }

theorem u1965 : Upper (D 1) (R 1) [304,68,136,3,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1965
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1966 : Route 9 := (fun mask => (mask,id))

def c1966 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1966 : Upper (D 1) (R 1) [304,68,136,3,64,128] 13 := by
  apply FastRouting.sound _ _ [304,68,136,3,64,128] 13 (by decide) (choices 1) [2,16,32] r1966 c1966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u312
  · exact u313
  · exact u314

def b1967 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 305 70 148 11 18 40 224 224 480), lower := (rows 305 70 148 11 18 40 64 128 256), losses := [] }

theorem u1967 : Upper (D 1) (R 1) [304,68,144,3,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1967
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1968 : Route 9 := (fun mask => (mask,id))

def c1968 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1968 : Upper (D 1) (R 1) [304,68,144,3,2,64] 13 := by
  apply FastRouting.sound _ _ [304,68,144,3,2,64] 13 (by decide) (choices 1) [8,32,128] r1968 c1968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u315
  · exact u316
  · exact u317

def r1969 : Route 9 := (fun mask => (mask,id))

def c1969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1969 : Upper (D 1) (R 1) [304,68,144,3,2,128] 13 := by
  apply FastRouting.sound _ _ [304,68,144,3,2,128] 13 (by decide) (choices 1) [8,32] r1969 c1969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u318
  · exact u319

def r1970 : Route 9 := (fun mask => (mask,id))

def c1970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1970 : Upper (D 1) (R 1) [304,68,144,3,64,2] 13 := by
  apply FastRouting.sound _ _ [304,68,144,3,64,2] 13 (by decide) (choices 1) [8,32,128] r1970 c1970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u320
  · exact u321
  · exact u322

def b1971 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 70 148 11 80 40 226 162 418), lower := (rows 305 70 148 11 80 40 64 128 256), losses := [] }

theorem u1971 : Upper (D 1) (R 1) [304,68,144,3,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1971
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1972 : Route 9 := (fun mask => (mask,id))

def c1972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1972 : Upper (D 1) (R 1) [304,68,144,3,64,128] 13 := by
  apply FastRouting.sound _ _ [304,68,144,3,64,128] 13 (by decide) (choices 1) [2,8,32] r1972 c1972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u323
  · exact u324
  · exact u325

def b1973 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 305 70 148 42 18 33 200 200 456), lower := (rows 305 70 148 42 18 33 64 128 256), losses := [] }

theorem u1973 : Upper (D 1) (R 1) [304,68,144,34,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1973
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1974 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 305 70 148 42 18 40 193 193 449), lower := (rows 305 70 148 42 18 40 64 128 256), losses := [] }

theorem u1974 : Upper (D 1) (R 1) [304,68,144,34,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1974
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1975 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 305 70 148 42 18 96 201 137 393), lower := (rows 305 70 148 42 18 96 64 128 256), losses := [] }

theorem u1975 : Upper (D 1) (R 1) [304,68,144,34,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1975
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1976 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 148 42 18 160 73 201 329), lower := (rows 305 70 148 42 18 160 64 128 256), losses := [] }

theorem u1976 : Upper (D 1) (R 1) [304,68,144,34,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1976
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1977 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 70 148 42 80 33 202 138 394), lower := (rows 305 70 148 42 80 33 64 128 256), losses := [] }

theorem u1977 : Upper (D 1) (R 1) [304,68,144,34,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1977
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1978 : PairBound 9 := { available := 137, camps := [{ cop := 5, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 148 42 80 34 201 137 393), lower := (rows 305 70 148 42 80 34 64 128 256), losses := [] }

theorem u1978 : Upper (D 1) (R 1) [304,68,144,34,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1978
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1979 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 70 148 42 80 40 195 131 387), lower := (rows 305 70 148 42 80 40 64 128 256), losses := [] }

theorem u1979 : Upper (D 1) (R 1) [304,68,144,34,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1979
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1979
end Delivery.IrregularNine14.P01
