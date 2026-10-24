import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0004
import IrregularNine14P05C0005
import IrregularNine14P05C0006

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2040 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 402, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 26 76 41 400 36 99 163 291), lower := (rows 7 26 76 41 400 36 64 128 256), losses := [] }

theorem u2040 : Upper (D 5) (R 5) [6,24,72,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2040
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2041 : Route 9 := (fun mask => (mask,id))

def c2041 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2041 : Upper (D 5) (R 5) [6,24,72,129,288,1] 13 := by
  apply FastRouting.sound _ _ [6,24,72,129,288,1] 13 (by decide) (choices 1) [2,4,32] r2041 c2041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u292
  · exact u293
  · exact u294

def r2042 : Route 9 := (fun mask => (mask,id))

def c2042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2042 : Upper (D 5) (R 5) [6,24,72,129,288,2] 13 := by
  apply FastRouting.sound _ _ [6,24,72,129,288,2] 13 (by decide) (choices 1) [1,4,32] r2042 c2042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u295
  · exact u296
  · exact u297

def r2043 : Route 9 := (fun mask => (mask,id))

def c2043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2043 : Upper (D 5) (R 5) [6,24,72,129,288,4] 13 := by
  apply FastRouting.sound _ _ [6,24,72,129,288,4] 13 (by decide) (choices 1) [1,2,32] r2043 c2043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u298
  · exact u299
  · exact u300

def r2044 : Route 9 := (fun mask => (mask,id))

def c2044 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2044 : Upper (D 5) (R 5) [6,24,72,160,257,1] 13 := by
  apply FastRouting.sound _ _ [6,24,72,160,257,1] 13 (by decide) (choices 1) [2,4,32] r2044 c2044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u301
  · exact u302
  · exact u303

def r2045 : Route 9 := (fun mask => (mask,id))

def c2045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2045 : Upper (D 5) (R 5) [6,24,72,160,257,2] 13 := by
  apply FastRouting.sound _ _ [6,24,72,160,257,2] 13 (by decide) (choices 1) [1,4,32] r2045 c2045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u304
  · exact u305
  · exact u306

def r2046 : Route 9 := (fun mask => (mask,id))

def c2046 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2046 : Upper (D 5) (R 5) [6,24,72,160,257,4] 13 := by
  apply FastRouting.sound _ _ [6,24,72,160,257,4] 13 (by decide) (choices 1) [1,2,32] r2046 c2046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u307
  · exact u308
  · exact u309

def b2047 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 26 76 392 49 33 102 166 294), lower := (rows 7 26 76 392 49 33 64 128 256), losses := [] }

theorem u2047 : Upper (D 5) (R 5) [6,24,72,384,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2047
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2048 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 76 392 49 34 101 165 293), lower := (rows 7 26 76 392 49 34 64 128 256), losses := [] }

theorem u2048 : Upper (D 5) (R 5) [6,24,72,384,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2048
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2049 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 394, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 76 392 49 36 99 163 291), lower := (rows 7 26 76 392 49 36 64 128 256), losses := [] }

theorem u2049 : Upper (D 5) (R 5) [6,24,72,384,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2049
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2050 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 26 100 41 145 34 332 396 268), lower := (rows 7 26 100 41 145 34 64 128 256), losses := [] }

theorem u2050 : Upper (D 5) (R 5) [6,24,96,33,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2050
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2051 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 402, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 100 41 145 36 330 394 266), lower := (rows 7 26 100 41 145 36 64 128 256), losses := [] }

theorem u2051 : Upper (D 5) (R 5) [6,24,96,33,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2051
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2052 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 26 100 41 145 40 326 390 262), lower := (rows 7 26 100 41 145 40 64 128 256), losses := [] }

theorem u2052 : Upper (D 5) (R 5) [6,24,96,33,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2052
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2053 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 41 145 288 78 142 270), lower := (rows 7 26 100 41 145 288 64 128 256), losses := [] }

theorem u2053 : Upper (D 5) (R 5) [6,24,96,33,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2053
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2054 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 26 100 41 148 33 330 394 266), lower := (rows 7 26 100 41 148 33 64 128 256), losses := [] }

theorem u2054 : Upper (D 5) (R 5) [6,24,96,33,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2054
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2055 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 26 100 41 148 34 329 393 265), lower := (rows 7 26 100 41 148 34 64 128 256), losses := [] }

theorem u2055 : Upper (D 5) (R 5) [6,24,96,33,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2055
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2056 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 400, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 26 100 41 148 40 323 387 259), lower := (rows 7 26 100 41 148 40 64 128 256), losses := [] }

theorem u2056 : Upper (D 5) (R 5) [6,24,96,33,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2056
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2057 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 7 26 100 41 148 288 75 139 267), lower := (rows 7 26 100 41 148 288 64 128 256), losses := [] }

theorem u2057 : Upper (D 5) (R 5) [6,24,96,33,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2057
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2058 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 26 100 41 400 33 78 142 270), lower := (rows 7 26 100 41 400 33 64 128 256), losses := [] }

theorem u2058 : Upper (D 5) (R 5) [6,24,96,33,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2058
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2059 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 26 100 41 400 34 77 141 269), lower := (rows 7 26 100 41 400 34 64 128 256), losses := [] }

theorem u2059 : Upper (D 5) (R 5) [6,24,96,33,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2059
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2060 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 402, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 100 41 400 36 75 139 267), lower := (rows 7 26 100 41 400 36 64 128 256), losses := [] }

theorem u2060 : Upper (D 5) (R 5) [6,24,96,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2060
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2061 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 26 100 41 400 40 71 135 263), lower := (rows 7 26 100 41 400 40 64 128 256), losses := [] }

theorem u2061 : Upper (D 5) (R 5) [6,24,96,33,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2061
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2062 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 100 42 145 33 332 396 268), lower := (rows 7 26 100 42 145 33 64 128 256), losses := [] }

theorem u2062 : Upper (D 5) (R 5) [6,24,96,34,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2062
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2063 : PairBound 9 := { available := 265, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 100 42 145 36 329 393 265), lower := (rows 7 26 100 42 145 36 64 128 256), losses := [] }

theorem u2063 : Upper (D 5) (R 5) [6,24,96,34,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2063
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2064 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 42 145 40 325 389 261), lower := (rows 7 26 100 42 145 40 64 128 256), losses := [] }

theorem u2064 : Upper (D 5) (R 5) [6,24,96,34,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2064
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2065 : Route 9 := (fun mask => (mask,id))

def c2065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2065 : Upper (D 5) (R 5) [6,24,96,34,129,256] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34,129,256] 13 (by decide) (choices 1) [1,4,8] r2065 c2065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u310
  · exact u311
  · exact u312

def r2066 : Route 9 := (fun mask => (mask,id))

def c2066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u2066 : Upper (D 5) (R 5) [6,24,96,34,132,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34,132,1] 13 (by decide) (choices 1) [1,8,256] r2066 c2066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u313
  · exact u314
  · exact u315

def b2067 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 42 148 40 321 385 257), lower := (rows 7 26 100 42 148 40 64 128 256), losses := [] }

theorem u2067 : Upper (D 5) (R 5) [6,24,96,34,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2067
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2068 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 7 26 100 42 148 288 73 137 265), lower := (rows 7 26 100 42 148 288 64 128 256), losses := [] }

theorem u2068 : Upper (D 5) (R 5) [6,24,96,34,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2068
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2069 : Route 9 := (fun mask => (mask,id))

def c2069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2069 : Upper (D 5) (R 5) [6,24,96,34,384,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34,384,1] 13 (by decide) (choices 1) [1,4,8] r2069 c2069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u316
  · exact u317
  · exact u318

def b2070 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 100 42 400 36 73 137 265), lower := (rows 7 26 100 42 400 36 64 128 256), losses := [] }

theorem u2070 : Upper (D 5) (R 5) [6,24,96,34,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2070
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2071 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 42 400 40 69 133 261), lower := (rows 7 26 100 42 400 40 64 128 256), losses := [] }

theorem u2071 : Upper (D 5) (R 5) [6,24,96,34,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2071
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2072 : Route 9 := (fun mask => (mask,id))

def c2072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2072 : Upper (D 5) (R 5) [6,24,96,129,257,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,257,2] 13 (by decide) (choices 1) [4,8,32] r2072 c2072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u319
  · exact u320
  · exact u321

def b2073 : PairBound 9 := { available := 42, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 100 137 273 36 106 170 298), lower := (rows 7 26 100 137 273 36 64 128 256), losses := [] }

theorem u2073 : Upper (D 5) (R 5) [6,24,96,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2073
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2074 : Route 9 := (fun mask => (mask,id))

def c2074 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2074 : Upper (D 5) (R 5) [6,24,96,129,257,8] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,257,8] 13 (by decide) (choices 1) [2,4,32] r2074 c2074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u322
  · exact u323
  · exact u324

def r2075 : Route 9 := (fun mask => (mask,id))

def c2075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2075 : Upper (D 5) (R 5) [6,24,96,129,260,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,260,1] 13 (by decide) (choices 1) [2,8,32] r2075 c2075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u325
  · exact u326
  · exact u327

def r2076 : Route 9 := (fun mask => (mask,id))

def c2076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2076 : Upper (D 5) (R 5) [6,24,96,129,260,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,260,2] 13 (by decide) (choices 1) [1,8,32] r2076 c2076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u328
  · exact u329
  · exact u330

def r2077 : Route 9 := (fun mask => (mask,id))

def c2077 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2077 : Upper (D 5) (R 5) [6,24,96,129,260,8] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,260,8] 13 (by decide) (choices 1) [1,2,32] r2077 c2077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u331
  · exact u332
  · exact u333

def b2078 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 7 26 100 137 304 33 78 142 270), lower := (rows 7 26 100 137 304 33 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 41 16 0 65 129 257), good := (rows 463 26 76 457 282 457 64 128 256) }] }

theorem u2078 : Upper (D 5) (R 5) [6,24,96,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2078
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2079 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 26 100 137 304 34 77 141 269), lower := (rows 7 26 100 137 304 34 64 128 256), losses := [] }

theorem u2079 : Upper (D 5) (R 5) [6,24,96,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2079
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2080 : PairBound 9 := { available := 11, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 100 137 304 36 75 139 267), lower := (rows 7 26 100 137 304 36 64 128 256), losses := [] }

theorem u2080 : Upper (D 5) (R 5) [6,24,96,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2080
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2081 : Route 9 := (fun mask => (mask,id))

def c2081 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2081 : Upper (D 5) (R 5) [6,24,96,129,288,8] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288,8] 13 (by decide) (choices 1) [1,2,4] r2081 c2081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u334
  · exact u335
  · exact u336

def b2082 : PairBound 9 := { available := 44, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 26 100 138 273 33 108 172 300), lower := (rows 7 26 100 138 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 8 17 49 66 130 258), good := (rows 501 508 100 460 309 53 64 128 256) }] }

theorem u2082 : Upper (D 5) (R 5) [6,24,96,130,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2082
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2083 : PairBound 9 := { available := 41, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 100 138 273 36 105 169 297), lower := (rows 7 26 100 138 273 36 64 128 256), losses := [] }

theorem u2083 : Upper (D 5) (R 5) [6,24,96,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2083
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2084 : PairBound 9 := { available := 37, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 26 100 138 273 40 101 165 293), lower := (rows 7 26 100 138 273 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 42 65 129 257), good := (rows 501 56 100 168 469 40 64 128 256) }] }

theorem u2084 : Upper (D 5) (R 5) [6,24,96,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2084
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2085 : Route 9 := (fun mask => (mask,id))

def c2085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2085 : Upper (D 5) (R 5) [6,24,96,130,260,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130,260,1] 13 (by decide) (choices 1) [1,8,32] r2085 c2085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u337
  · exact u338
  · exact u339

def b2086 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 168, targets := 4 }], pairs := [(2,1),(3,2)], upper := (rows 7 26 100 138 276 40 97 161 289), lower := (rows 7 26 100 138 276 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 42 65 129 257), good := (rows 501 56 100 168 276 40 64 128 256) }] }

theorem u2086 : Upper (D 5) (R 5) [6,24,96,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2086
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2087 : Route 9 := (fun mask => (mask,id))

def c2087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2087 : Upper (D 5) (R 5) [6,24,96,130,288,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130,288,1] 13 (by decide) (choices 1) [1,4,8] r2087 c2087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u340
  · exact u341
  · exact u342

def b2088 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 100 138 304 36 73 137 265), lower := (rows 7 26 100 138 304 36 64 128 256), losses := [] }

theorem u2088 : Upper (D 5) (R 5) [6,24,96,130,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2088
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2089 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(2,1),(3,5)], upper := (rows 7 26 100 138 304 40 69 133 261), lower := (rows 7 26 100 138 304 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 42 65 129 257), good := (rows 501 56 100 168 304 40 64 128 256) }] }

theorem u2089 : Upper (D 5) (R 5) [6,24,96,130,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2089
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2090 : Route 9 := (fun mask => (mask,id))

def c2090 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2090 : Upper (D 5) (R 5) [6,24,96,132,257,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,132,257,1] 13 (by decide) (choices 1) [2,8,32] r2090 c2090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u343
  · exact u344
  · exact u345

def r2091 : Route 9 := (fun mask => (mask,id))

def c2091 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2091 : Upper (D 5) (R 5) [6,24,96,132,257,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,132,257,2] 13 (by decide) (choices 1) [1,8,32] r2091 c2091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u346
  · exact u347
  · exact u348

def r2092 : Route 9 := (fun mask => (mask,id))

def c2092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2092 : Upper (D 5) (R 5) [6,24,96,132,257,8] 13 := by
  apply FastRouting.sound _ _ [6,24,96,132,257,8] 13 (by decide) (choices 1) [1,2,32] r2092 c2092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u349
  · exact u350
  · exact u351

def r2093 : Route 9 := (fun mask => (mask,id))

def c2093 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2093 : Upper (D 5) (R 5) [6,24,96,132,288,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,132,288,1] 13 (by decide) (choices 1) [1,2,8] r2093 c2093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u352
  · exact u353
  · exact u354

def b2094 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 26 100 140 304 34 73 137 265), lower := (rows 7 26 100 140 304 34 64 128 256), losses := [] }

theorem u2094 : Upper (D 5) (R 5) [6,24,96,132,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2094
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2095 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5),(4,2)], upper := (rows 7 26 100 140 304 40 67 131 259), lower := (rows 7 26 100 140 304 40 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 17 42 65 129 257), good := (rows 499 58 96 168 304 40 64 128 256) }] }

theorem u2095 : Upper (D 5) (R 5) [6,24,96,132,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2095
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2096 : Route 9 := (fun mask => (mask,id))

def c2096 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2096 : Upper (D 5) (R 5) [6,24,96,160,257,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,257,1] 13 (by decide) (choices 1) [2,4,8] r2096 c2096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u355
  · exact u356
  · exact u357

def r2097 : Route 9 := (fun mask => (mask,id))

def c2097 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2097 : Upper (D 5) (R 5) [6,24,96,160,257,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,257,2] 13 (by decide) (choices 1) [1,4,8] r2097 c2097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u358
  · exact u359
  · exact u360

def b2098 : PairBound 9 := { available := 11, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 100 168 273 36 75 139 267), lower := (rows 7 26 100 168 273 36 64 128 256), losses := [] }

theorem u2098 : Upper (D 5) (R 5) [6,24,96,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2098
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2099 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 26 100 168 273 40 71 135 263), lower := (rows 7 26 100 168 273 40 64 128 256), losses := [] }

theorem u2099 : Upper (D 5) (R 5) [6,24,96,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2099
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2099
end Delivery.IrregularNine14.P05
