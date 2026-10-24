import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0006

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2040 : Route 9 := (fun mask => (mask,id))

def c2040 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2040 : Upper (D 1) (R 1) [304,80,65,132,128,2] 13 := by
  apply FastRouting.sound _ _ [304,80,65,132,128,2] 13 (by decide) (choices 1) [2,8,32] r2040 c2040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u362
  · exact u363
  · exact u364

def b2041 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 82 69 140 144 40 98 162 290), lower := (rows 305 82 69 140 144 40 64 128 256), losses := [] }

theorem u2041 : Upper (D 1) (R 1) [304,80,65,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2041
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2042 : Route 9 := (fun mask => (mask,id))

def c2042 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2042 : Upper (D 1) (R 1) [304,80,65,160,128,2] 13 := by
  apply FastRouting.sound _ _ [304,80,65,160,128,2] 13 (by decide) (choices 1) [2,4,8] r2042 c2042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u365
  · exact u366
  · exact u367

def b2043 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 82 69 168 144 36 74 138 266), lower := (rows 305 82 69 168 144 36 64 128 256), losses := [] }

theorem u2043 : Upper (D 1) (R 1) [304,80,65,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2043
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2044 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 305 82 69 168 144 40 70 134 262), lower := (rows 305 82 69 168 144 40 64 128 256), losses := [] }

theorem u2044 : Upper (D 1) (R 1) [304,80,65,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2044
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2045 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 100 137 144 34 78 142 270), lower := (rows 305 82 100 137 144 34 64 128 256), losses := [] }

theorem u2045 : Upper (D 1) (R 1) [304,80,96,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2045
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2046 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 82 100 137 144 36 74 138 266), lower := (rows 305 82 100 137 144 36 64 128 256), losses := [] }

theorem u2046 : Upper (D 1) (R 1) [304,80,96,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2046
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2047 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 305 82 100 137 144 40 70 134 262), lower := (rows 305 82 100 137 144 40 64 128 256), losses := [] }

theorem u2047 : Upper (D 1) (R 1) [304,80,96,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2047
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2048 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 305 82 100 138 144 33 78 142 270), lower := (rows 305 82 100 138 144 33 64 128 256), losses := [] }

theorem u2048 : Upper (D 1) (R 1) [304,80,96,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2048
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2049 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 100 138 144 34 77 141 269), lower := (rows 305 82 100 138 144 34 64 128 256), losses := [] }

theorem u2049 : Upper (D 1) (R 1) [304,80,96,130,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2049
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2050 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 305 82 100 138 144 36 75 139 267), lower := (rows 305 82 100 138 144 36 64 128 256), losses := [] }

theorem u2050 : Upper (D 1) (R 1) [304,80,96,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2050
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2051 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 305 82 100 138 144 40 71 135 263), lower := (rows 305 82 100 138 144 40 64 128 256), losses := [] }

theorem u2051 : Upper (D 1) (R 1) [304,80,96,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2051
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2052 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 82 100 140 144 33 74 138 266), lower := (rows 305 82 100 140 144 33 64 128 256), losses := [] }

theorem u2052 : Upper (D 1) (R 1) [304,80,96,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2052
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2053 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 100 140 144 34 75 139 267), lower := (rows 305 82 100 140 144 34 64 128 256), losses := [] }

theorem u2053 : Upper (D 1) (R 1) [304,80,96,132,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2053
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2054 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 82 100 140 144 40 67 131 259), lower := (rows 305 82 100 140 144 40 64 128 256), losses := [] }

theorem u2054 : Upper (D 1) (R 1) [304,80,96,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2054
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2055 : PairBound 9 := { available := 56, camps := [], pairs := [(0,6)], upper := (rows 305 194 7 76 18 160 120 184 312), lower := (rows 305 194 7 76 18 160 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 22 170 0 136 264), good := (rows 305 178 55 445 50 160 0 160 256) }] }

theorem u2055 : Upper (D 1) (R 1) [304,192,3,68,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2055
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2056 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 194 7 76 24 160 114 178 306), lower := (rows 305 194 7 76 24 160 64 128 256), losses := [] }

theorem u2056 : Upper (D 1) (R 1) [304,192,3,68,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2056
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2057 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 7 76 48 160 90 154 282), lower := (rows 305 194 7 76 48 160 64 128 256), losses := [] }

theorem u2057 : Upper (D 1) (R 1) [304,192,3,68,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2057
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2058 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 194 13 14 18 96 240 176 432), lower := (rows 305 194 13 14 18 96 64 128 256), losses := [] }

theorem u2058 : Upper (D 1) (R 1) [304,192,9,6,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2058
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2059 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 13 14 48 96 210 146 402), lower := (rows 305 194 13 14 48 96 64 128 256), losses := [] }

theorem u2059 : Upper (D 1) (R 1) [304,192,9,6,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2059
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2060 : Route 9 := (fun mask => (mask,id))

def c2060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2060 : Upper (D 1) (R 1) [304,192,9,6,64,128] 13 := by
  apply FastRouting.sound _ _ [304,192,9,6,64,128] 13 (by decide) (choices 1) [2,16,32] r2060 c2060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u368
  · exact u369
  · exact u370

def b2061 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 305 194 28 104 18 33 198 134 390), lower := (rows 305 194 28 104 18 33 64 128 256), losses := [] }

theorem u2061 : Upper (D 1) (R 1) [304,192,24,96,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2061
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2062 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 28 104 18 34 197 133 389), lower := (rows 305 194 28 104 18 34 64 128 256), losses := [] }

theorem u2062 : Upper (D 1) (R 1) [304,192,24,96,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2062
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2063 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 194 28 104 18 36 195 131 387), lower := (rows 305 194 28 104 18 36 64 128 256), losses := [] }

theorem u2063 : Upper (D 1) (R 1) [304,192,24,96,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2063
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2064 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 305 194 28 104 18 160 71 135 263), lower := (rows 305 194 28 104 18 160 64 128 256), losses := [] }

theorem u2064 : Upper (D 1) (R 1) [304,192,24,96,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2064
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2065 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 305 194 28 104 144 33 70 134 262), lower := (rows 305 194 28 104 144 33 64 128 256), losses := [] }

theorem u2065 : Upper (D 1) (R 1) [304,192,24,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2065
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2066 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 305 194 28 104 144 34 71 135 263), lower := (rows 305 194 28 104 144 34 64 128 256), losses := [] }

theorem u2066 : Upper (D 1) (R 1) [304,192,24,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2066
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2067 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 194 28 104 144 36 67 131 259), lower := (rows 305 194 28 104 144 36 64 128 256), losses := [] }

theorem u2067 : Upper (D 1) (R 1) [304,192,24,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2067
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2068 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 69 140 18 34 120 184 312), lower := (rows 305 194 69 140 18 34 64 128 256), losses := [] }

theorem u2068 : Upper (D 1) (R 1) [304,192,65,132,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2068
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2069 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 194 69 140 18 40 114 178 306), lower := (rows 305 194 69 140 18 40 64 128 256), losses := [] }

theorem u2069 : Upper (D 1) (R 1) [304,192,65,132,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2069
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2070 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 206, targets := 16 }], pairs := [(1,4)], upper := (rows 305 194 69 140 18 48 106 170 298), lower := (rows 305 194 69 140 18 48 64 128 256), losses := [] }

theorem u2070 : Upper (D 1) (R 1) [304,192,65,132,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2070
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2071 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 15 19 100 392 18 240 240 240 496), lower := (rows 15 19 100 392 18 32 64 128 256), losses := [] }

theorem u2071 : Upper (D 1) (R 1) [14,17,96,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2071
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2072 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 15 19 100 392 48 242 210 210 466), lower := (rows 15 19 100 392 48 32 64 128 256), losses := [] }

theorem u2072 : Upper (D 1) (R 1) [14,17,96,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2072
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2073 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 15 19 100 392 144 114 114 242 370), lower := (rows 15 19 100 392 144 32 64 128 256), losses := [] }

theorem u2073 : Upper (D 1) (R 1) [14,17,96,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2073
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2074 : PairBound 9 := { available := 240, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 15 50 69 392 18 240 240 240 496), lower := (rows 15 50 69 392 18 32 64 128 256), losses := [] }

theorem u2074 : Upper (D 1) (R 1) [14,48,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2074
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2075 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 15 50 69 392 48 242 210 210 466), lower := (rows 15 50 69 392 48 32 64 128 256), losses := [] }

theorem u2075 : Upper (D 1) (R 1) [14,48,65,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2075
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2076 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 15 50 69 392 80 178 242 178 434), lower := (rows 15 50 69 392 80 32 64 128 256), losses := [] }

theorem u2076 : Upper (D 1) (R 1) [14,48,65,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2076
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2077 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 15 50 69 392 144 114 114 242 370), lower := (rows 15 50 69 392 144 32 64 128 256), losses := [] }

theorem u2077 : Upper (D 1) (R 1) [14,48,65,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2077
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2078 : PairBound 9 := { available := 240, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 15 50 196 265 18 240 240 240 496), lower := (rows 15 50 196 265 18 32 64 128 256), losses := [] }

theorem u2078 : Upper (D 1) (R 1) [14,48,192,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2078
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2079 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 15 50 196 265 48 242 210 210 466), lower := (rows 15 50 196 265 48 32 64 128 256), losses := [] }

theorem u2079 : Upper (D 1) (R 1) [14,48,192,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2079
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2080 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 15 50 196 265 80 178 242 178 434), lower := (rows 15 50 196 265 80 32 64 128 256), losses := [] }

theorem u2080 : Upper (D 1) (R 1) [14,48,192,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2080
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2081 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 15 259 52 200 18 240 240 240 496), lower := (rows 15 259 52 200 18 32 64 128 256), losses := [] }

theorem u2081 : Upper (D 1) (R 1) [14,257,48,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2081
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2082 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 15 259 52 200 48 242 210 210 466), lower := (rows 15 259 52 200 48 32 64 128 256), losses := [] }

theorem u2082 : Upper (D 1) (R 1) [14,257,48,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2082
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2083_2 : Upper (D 1) (R 1) [14,257,48,192,64,2] 13 :=
  permutation_upper _ _ _ [14,257,48,192,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u371

theorem m2083_16 : Upper (D 1) (R 1) [14,257,48,192,64,16] 13 :=
  permutation_upper _ _ _ [14,257,48,192,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u372

def r2083 : Route 9 := (fun mask => (mask,id))

def c2083 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2083 : Upper (D 1) (R 1) [14,257,48,192,64] 13 := by
  apply FastRouting.sound _ _ [14,257,48,192,64] 13 (by decide) (choices 1) [2,16,128] r2083 c2083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2083_2
  · exact m2083_16
  · exact u373

def b2084 : PairBound 9 := { available := 240, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 15 274 37 200 18 240 240 240 496), lower := (rows 15 274 37 200 18 32 64 128 256), losses := [] }

theorem u2084 : Upper (D 1) (R 1) [14,272,33,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2084
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2085 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 15 274 37 200 48 242 210 210 466), lower := (rows 15 274 37 200 48 32 64 128 256), losses := [] }

theorem u2085 : Upper (D 1) (R 1) [14,272,33,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2085
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2086 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 15 274 37 200 80 178 242 178 434), lower := (rows 15 274 37 200 80 32 64 128 256), losses := [] }

theorem u2086 : Upper (D 1) (R 1) [14,272,33,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2086
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2087 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 100 168 18 496 464 464 464), lower := (rows 23 11 100 168 18 32 64 128 256), losses := [] }

theorem u2087 : Upper (D 1) (R 1) [22,9,96,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2087
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2088 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 11 100 168 80 434 466 402 402), lower := (rows 23 11 100 168 80 32 64 128 256), losses := [] }

theorem u2088 : Upper (D 1) (R 1) [22,9,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2088
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2089 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 356, targets := 128 }], pairs := [(2,7)], upper := (rows 23 11 100 168 144 370 338 466 338), lower := (rows 23 11 100 168 144 32 64 128 256), losses := [] }

theorem u2089 : Upper (D 1) (R 1) [22,9,96,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2089
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2090 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 11 100 168 272 242 210 210 466), lower := (rows 23 11 100 168 272 32 64 128 256), losses := [] }

theorem u2090 : Upper (D 1) (R 1) [22,9,96,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2090
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2091 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 100 296 18 240 208 208 464), lower := (rows 23 11 100 296 18 32 64 128 256), losses := [] }

theorem u2091 : Upper (D 1) (R 1) [22,9,96,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2091
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2092 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 11 100 296 80 178 210 146 402), lower := (rows 23 11 100 296 80 32 64 128 256), losses := [] }

theorem u2092 : Upper (D 1) (R 1) [22,9,96,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2092
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2093 : Route 9 := (fun mask => (mask,id))

def c2093 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2093 : Upper (D 1) (R 1) [22,9,96,288,128] 13 := by
  apply FastRouting.sound _ _ [22,9,96,288,128] 13 (by decide) (choices 1) [2,16,64,128] r2093 c2093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u374
  · exact u375
  · exact u376
  · exact u377

def b2094 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 100 392 18 240 240 240 496), lower := (rows 23 11 100 392 18 32 64 128 256), losses := [] }

theorem u2094 : Upper (D 1) (R 1) [22,9,96,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2094
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2095 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 23 11 100 392 48 242 210 210 466), lower := (rows 23 11 100 392 48 32 64 128 256), losses := [] }

theorem u2095 : Upper (D 1) (R 1) [22,9,96,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2095
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2096 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 23 11 100 392 144 114 114 242 370), lower := (rows 23 11 100 392 144 32 64 128 256), losses := [] }

theorem u2096 : Upper (D 1) (R 1) [22,9,96,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2096
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2097 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 292 104 18 240 208 208 464), lower := (rows 23 11 292 104 18 32 64 128 256), losses := [] }

theorem u2097 : Upper (D 1) (R 1) [22,9,288,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2097
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2098 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 23 11 292 104 80 178 210 146 402), lower := (rows 23 11 292 104 80 32 64 128 256), losses := [] }

theorem u2098 : Upper (D 1) (R 1) [22,9,288,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2098
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2099 : Route 9 := (fun mask => (mask,id))

def c2099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2099 : Upper (D 1) (R 1) [22,9,288,96,128] 13 := by
  apply FastRouting.sound _ _ [22,9,288,96,128] 13 (by decide) (choices 1) [2,16,64,128] r2099 c2099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u378
  · exact u379
  · exact u380
  · exact u381

#print axioms u2099
end Delivery.IrregularNine14.P01
