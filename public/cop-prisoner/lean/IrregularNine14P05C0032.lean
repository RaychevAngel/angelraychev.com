import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0003
import IrregularNine14P05C0004

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1920 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 42 400 33 76 140 268), lower := (rows 7 19 100 42 400 33 64 128 256), losses := [] }

theorem u1920 : Upper (D 5) (R 5) [6,17,96,34,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1920
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1921 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 42 400 36 73 137 265), lower := (rows 7 19 100 42 400 36 64 128 256), losses := [] }

theorem u1921 : Upper (D 5) (R 5) [6,17,96,34,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1921
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1922 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 19 100 42 400 40 77 141 269), lower := (rows 7 19 100 42 400 40 64 128 256), losses := [] }

theorem u1922 : Upper (D 5) (R 5) [6,17,96,34,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1922
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1923 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 392, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 100 137 56 34 332 396 268), lower := (rows 7 19 100 137 56 34 64 128 256), losses := [] }

theorem u1923 : Upper (D 5) (R 5) [6,17,96,129,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1923
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1924 : PairBound 9 := { available := 266, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 137 56 36 330 394 266), lower := (rows 7 19 100 137 56 36 64 128 256), losses := [] }

theorem u1924 : Upper (D 5) (R 5) [6,17,96,129,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1924
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1925 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 327, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 137 56 40 326 390 262), lower := (rows 7 19 100 137 56 40 64 128 256), losses := [] }

theorem u1925 : Upper (D 5) (R 5) [6,17,96,129,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1925
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1926 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 19 100 137 56 288 78 142 270), lower := (rows 7 19 100 137 56 288 64 128 256), losses := [] }

theorem u1926 : Upper (D 5) (R 5) [6,17,96,129,40,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1926
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1927 : PairBound 9 := { available := 44, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 19 100 137 280 34 108 172 300), lower := (rows 7 19 100 137 280 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 35 72 136 264), good := (rows 38 50 100 508 476 34 64 128 256) }] }

theorem u1927 : Upper (D 5) (R 5) [6,17,96,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1927
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1928 : PairBound 9 := { available := 42, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 137 280 36 106 170 298), lower := (rows 7 19 100 137 280 36 64 128 256), losses := [] }

theorem u1928 : Upper (D 5) (R 5) [6,17,96,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1928
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1929 : Route 9 := (fun mask => (mask,id))

def c1929 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1929 : Upper (D 5) (R 5) [6,17,96,129,264,8] 13 := by
  apply FastRouting.sound _ _ [6,17,96,129,264,8] 13 (by decide) (choices 1) [2,4,32] r1929 c1929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u221
  · exact u222
  · exact u223

def b1930 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 100 137 304 34 76 140 268), lower := (rows 7 19 100 137 304 34 64 128 256), losses := [] }

theorem u1930 : Upper (D 5) (R 5) [6,17,96,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1930
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1931 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 137 304 36 74 138 266), lower := (rows 7 19 100 137 304 36 64 128 256), losses := [] }

theorem u1931 : Upper (D 5) (R 5) [6,17,96,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1931
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1932 : Route 9 := (fun mask => (mask,id))

def c1932 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1932 : Upper (D 5) (R 5) [6,17,96,129,288,8] 13 := by
  apply FastRouting.sound _ _ [6,17,96,129,288,8] 13 (by decide) (choices 1) [2,4,8] r1932 c1932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u224
  · exact u225
  · exact u226

def b1933 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 324, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 138 56 33 332 396 268), lower := (rows 7 19 100 138 56 33 64 128 256), losses := [] }

theorem u1933 : Upper (D 5) (R 5) [6,17,96,130,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1933
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1934 : PairBound 9 := { available := 265, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 138 56 36 329 393 265), lower := (rows 7 19 100 138 56 36 64 128 256), losses := [] }

theorem u1934 : Upper (D 5) (R 5) [6,17,96,130,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1934
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1935 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 100 138 56 40 325 389 261), lower := (rows 7 19 100 138 56 40 64 128 256), losses := [] }

theorem u1935 : Upper (D 5) (R 5) [6,17,96,130,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1935
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1936 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 19 100 138 56 288 77 141 269), lower := (rows 7 19 100 138 56 288 64 128 256), losses := [] }

theorem u1936 : Upper (D 5) (R 5) [6,17,96,130,40,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1936
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1937 : PairBound 9 := { available := 44, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 19 100 138 280 33 108 172 300), lower := (rows 7 19 100 138 280 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 35 72 136 264), good := (rows 37 49 100 508 476 33 64 128 256) }] }

theorem u1937 : Upper (D 5) (R 5) [6,17,96,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1937
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1938 : PairBound 9 := { available := 41, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 138 280 36 105 169 297), lower := (rows 7 19 100 138 280 36 64 128 256), losses := [] }

theorem u1938 : Upper (D 5) (R 5) [6,17,96,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1938
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1939 : PairBound 9 := { available := 37, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 19 100 138 280 40 101 165 293), lower := (rows 7 19 100 138 280 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 14 8 24 56 66 130 258), good := (rows 453 501 100 508 316 60 64 128 256) }] }

theorem u1939 : Upper (D 5) (R 5) [6,17,96,130,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1939
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1940 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 136, targets := 1 },{ cop := 0, region := 136, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 100 138 304 33 76 140 268), lower := (rows 7 19 100 138 304 33 64 128 256), losses := [] }

theorem u1940 : Upper (D 5) (R 5) [6,17,96,130,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1940
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1941 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 138 304 36 73 137 265), lower := (rows 7 19 100 138 304 36 64 128 256), losses := [] }

theorem u1941 : Upper (D 5) (R 5) [6,17,96,130,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1941
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1942 : Route 9 := (fun mask => (mask,id))

def c1942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1942 : Upper (D 5) (R 5) [6,17,96,130,288,8] 13 := by
  apply FastRouting.sound _ _ [6,17,96,130,288,8] 13 (by decide) (choices 1) [1,4,8] r1942 c1942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u227
  · exact u228
  · exact u229

def b1943 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 392, targets := 1 },{ cop := 0, region := 392, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 100 140 56 33 330 394 266), lower := (rows 7 19 100 140 56 33 64 128 256), losses := [] }

theorem u1943 : Upper (D 5) (R 5) [6,17,96,132,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1943
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1944 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 392, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 100 140 56 34 329 393 265), lower := (rows 7 19 100 140 56 34 64 128 256), losses := [] }

theorem u1944 : Upper (D 5) (R 5) [6,17,96,132,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1944
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1945 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 100 140 56 40 323 387 259), lower := (rows 7 19 100 140 56 40 64 128 256), losses := [] }

theorem u1945 : Upper (D 5) (R 5) [6,17,96,132,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1945
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1946 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 19 100 140 56 288 75 139 267), lower := (rows 7 19 100 140 56 288 64 128 256), losses := [] }

theorem u1946 : Upper (D 5) (R 5) [6,17,96,132,40,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1946
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1947 : Route 9 := (fun mask => (mask,id))

def c1947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1947 : Upper (D 5) (R 5) [6,17,96,132,264,1] 13 := by
  apply FastRouting.sound _ _ [6,17,96,132,264,1] 13 (by decide) (choices 1) [2,8,32] r1947 c1947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u230
  · exact u231
  · exact u232

def r1948 : Route 9 := (fun mask => (mask,id))

def c1948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1948 : Upper (D 5) (R 5) [6,17,96,132,264,2] 13 := by
  apply FastRouting.sound _ _ [6,17,96,132,264,2] 13 (by decide) (choices 1) [1,8,32] r1948 c1948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u233
  · exact u234
  · exact u235

def r1949 : Route 9 := (fun mask => (mask,id))

def c1949 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1949 : Upper (D 5) (R 5) [6,17,96,132,264,8] 13 := by
  apply FastRouting.sound _ _ [6,17,96,132,264,8] 13 (by decide) (choices 1) [1,2,32] r1949 c1949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u236
  · exact u237
  · exact u238

def b1950 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 136, targets := 1 },{ cop := 0, region := 136, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 100 140 304 33 74 138 266), lower := (rows 7 19 100 140 304 33 64 128 256), losses := [] }

theorem u1950 : Upper (D 5) (R 5) [6,17,96,132,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1950
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1951 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 100 140 304 34 73 137 265), lower := (rows 7 19 100 140 304 34 64 128 256), losses := [] }

theorem u1951 : Upper (D 5) (R 5) [6,17,96,132,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1951
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1952 : Route 9 := (fun mask => (mask,id))

def c1952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1952 : Upper (D 5) (R 5) [6,17,96,132,288,8] 13 := by
  apply FastRouting.sound _ _ [6,17,96,132,288,8] 13 (by decide) (choices 1) [1,2,8] r1952 c1952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u239
  · exact u240
  · exact u241

def r1953 : Route 9 := (fun mask => (mask,id))

def c1953 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1953 : Upper (D 5) (R 5) [6,17,96,160,264,1] 13 := by
  apply FastRouting.sound _ _ [6,17,96,160,264,1] 13 (by decide) (choices 1) [2,4,8] r1953 c1953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u242
  · exact u243
  · exact u244

def r1954 : Route 9 := (fun mask => (mask,id))

def c1954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1954 : Upper (D 5) (R 5) [6,17,96,160,264,2] 13 := by
  apply FastRouting.sound _ _ [6,17,96,160,264,2] 13 (by decide) (choices 1) [1,4,8] r1954 c1954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u245
  · exact u246
  · exact u247

def b1955 : PairBound 9 := { available := 11, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 168 280 36 75 139 267), lower := (rows 7 19 100 168 280 36 64 128 256), losses := [] }

theorem u1955 : Upper (D 5) (R 5) [6,17,96,160,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1955
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1956 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 19 100 168 280 40 71 135 263), lower := (rows 7 19 100 168 280 40 64 128 256), losses := [] }

theorem u1956 : Upper (D 5) (R 5) [6,17,96,160,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1956
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1957 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 392, targets := 1 },{ cop := 0, region := 392, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 100 392 56 33 78 142 270), lower := (rows 7 19 100 392 56 33 64 128 256), losses := [] }

theorem u1957 : Upper (D 5) (R 5) [6,17,96,384,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1957
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1958 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 392, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 100 392 56 34 77 141 269), lower := (rows 7 19 100 392 56 34 64 128 256), losses := [] }

theorem u1958 : Upper (D 5) (R 5) [6,17,96,384,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1958
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1959 : PairBound 9 := { available := 11, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 100 392 56 36 75 139 267), lower := (rows 7 19 100 392 56 36 64 128 256), losses := [] }

theorem u1959 : Upper (D 5) (R 5) [6,17,96,384,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1959
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1960 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 100 392 56 40 71 135 263), lower := (rows 7 19 100 392 56 40 64 128 256), losses := [] }

theorem u1960 : Upper (D 5) (R 5) [6,17,96,384,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1960
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1961 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 196, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 196 41 280 34 108 172 300), lower := (rows 7 19 196 41 280 34 64 128 256), losses := [] }

theorem u1961 : Upper (D 5) (R 5) [6,17,192,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1961
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1962 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 274, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 19 196 41 280 36 106 170 298), lower := (rows 7 19 196 41 280 36 64 128 256), losses := [] }

theorem u1962 : Upper (D 5) (R 5) [6,17,192,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1962
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1963 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 19 196 41 280 40 102 166 294), lower := (rows 7 19 196 41 280 40 64 128 256), losses := [] }

theorem u1963 : Upper (D 5) (R 5) [6,17,192,33,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1963
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1964 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 196, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 196 41 304 34 76 140 268), lower := (rows 7 19 196 41 304 34 64 128 256), losses := [] }

theorem u1964 : Upper (D 5) (R 5) [6,17,192,33,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1964
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1965 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 274, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 19 196 41 304 36 74 138 266), lower := (rows 7 19 196 41 304 36 64 128 256), losses := [] }

theorem u1965 : Upper (D 5) (R 5) [6,17,192,33,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1965
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1966 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 19 196 41 304 40 78 142 270), lower := (rows 7 19 196 41 304 40 64 128 256), losses := [] }

theorem u1966 : Upper (D 5) (R 5) [6,17,192,33,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1966
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1967 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 196, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 196 42 280 33 108 172 300), lower := (rows 7 19 196 42 280 33 64 128 256), losses := [] }

theorem u1967 : Upper (D 5) (R 5) [6,17,192,34,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1967
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1968 : Route 9 := (fun mask => (mask,id))

def c1968 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1968 : Upper (D 5) (R 5) [6,17,192,34,264,4] 13 := by
  apply FastRouting.sound _ _ [6,17,192,34,264,4] 13 (by decide) (choices 1) [1,8,32] r1968 c1968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u248
  · exact u249
  · exact u250

def b1969 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 19 196 42 280 40 101 165 293), lower := (rows 7 19 196 42 280 40 64 128 256), losses := [] }

theorem u1969 : Upper (D 5) (R 5) [6,17,192,34,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1969
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1970 : Route 9 := (fun mask => (mask,id))

def c1970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1970 : Upper (D 5) (R 5) [6,17,192,36,264,1] 13 := by
  apply FastRouting.sound _ _ [6,17,192,36,264,1] 13 (by decide) (choices 1) [2,8,32] r1970 c1970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u251
  · exact u252
  · exact u253

def r1971 : Route 9 := (fun mask => (mask,id))

def c1971 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1971 : Upper (D 5) (R 5) [6,17,192,36,264,2] 13 := by
  apply FastRouting.sound _ _ [6,17,192,36,264,2] 13 (by decide) (choices 1) [1,8,32] r1971 c1971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u254
  · exact u255
  · exact u256

def b1972 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 19 196 44 280 40 99 163 291), lower := (rows 7 19 196 44 280 40 64 128 256), losses := [] }

theorem u1972 : Upper (D 5) (R 5) [6,17,192,36,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1972
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1973 : Route 9 := (fun mask => (mask,id))

def c1973 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1973 : Upper (D 5) (R 5) [6,17,192,36,288,1] 13 := by
  apply FastRouting.sound _ _ [6,17,192,36,288,1] 13 (by decide) (choices 1) [2,8] r1973 c1973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u257
  · exact u258

def b1974 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(2,1),(3,0)], upper := (rows 7 19 196 44 304 34 73 137 265), lower := (rows 7 19 196 44 304 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 39 56 48 32 66 130 258), good := (rows 453 477 196 60 316 508 64 128 256) }] }

theorem u1974 : Upper (D 5) (R 5) [6,17,192,36,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1974
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1975 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 19 196 44 304 40 75 139 267), lower := (rows 7 19 196 44 304 40 64 128 256), losses := [] }

theorem u1975 : Upper (D 5) (R 5) [6,17,192,36,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1975
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1976 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 50, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 19 196 265 56 34 108 172 300), lower := (rows 7 19 196 265 56 34 64 128 256), losses := [] }

theorem u1976 : Upper (D 5) (R 5) [6,17,192,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1976
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1977 : PairBound 9 := { available := 42, camps := [], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 265 56 36 106 170 298), lower := (rows 7 19 196 265 56 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 37 64 128 256), good := (rows 38 50 228 312 56 36 64 128 256) },{ target := 1, region := (rows 1 0 4 8 24 37 64 128 256), good := (rows 37 49 228 313 56 36 64 128 256) }] }

theorem u1977 : Upper (D 5) (R 5) [6,17,192,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1977
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1978 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 196 265 56 40 102 166 294), lower := (rows 7 19 196 265 56 40 64 128 256), losses := [] }

theorem u1978 : Upper (D 5) (R 5) [6,17,192,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1978
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1979 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 196, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 196 266 56 33 108 172 300), lower := (rows 7 19 196 266 56 33 64 128 256), losses := [] }

theorem u1979 : Upper (D 5) (R 5) [6,17,192,258,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1979
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1979
end Delivery.IrregularNine14.P05
