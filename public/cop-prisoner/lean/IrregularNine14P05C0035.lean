import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0006

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2100 : Route 9 := (fun mask => (mask,id))

def c2100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2100 : Upper (D 5) (R 5) [6,24,96,160,260,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,260,1] 13 (by decide) (choices 1) [1,2,8] r2100 c2100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u361
  · exact u362
  · exact u363

def r2101 : Route 9 := (fun mask => (mask,id))

def c2101 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2101 : Upper (D 5) (R 5) [6,24,96,160,260,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,260,2] 13 (by decide) (choices 1) [1,8] r2101 c2101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u364
  · exact u365

def b2102 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 26 100 168 276 40 67 131 259), lower := (rows 7 26 100 168 276 40 64 128 256), losses := [] }

theorem u2102 : Upper (D 5) (R 5) [6,24,96,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2102
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2103 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 26 196 41 273 34 108 172 300), lower := (rows 7 26 196 41 273 34 64 128 256), losses := [] }

theorem u2103 : Upper (D 5) (R 5) [6,24,192,33,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2103
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2104 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 274, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 26 196 41 273 36 106 170 298), lower := (rows 7 26 196 41 273 36 64 128 256), losses := [] }

theorem u2104 : Upper (D 5) (R 5) [6,24,192,33,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2104
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2105 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 26 196 41 273 40 102 166 294), lower := (rows 7 26 196 41 273 40 64 128 256), losses := [] }

theorem u2105 : Upper (D 5) (R 5) [6,24,192,33,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2105
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2106 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 26 196 41 276 33 106 170 298), lower := (rows 7 26 196 41 276 33 64 128 256), losses := [] }

theorem u2106 : Upper (D 5) (R 5) [6,24,192,33,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2106
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2107 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 26 196 41 276 34 105 169 297), lower := (rows 7 26 196 41 276 34 64 128 256), losses := [] }

theorem u2107 : Upper (D 5) (R 5) [6,24,192,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2107
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2108 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 40, targets := 2 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 7 26 196 41 276 40 99 163 291), lower := (rows 7 26 196 41 276 40 64 128 256), losses := [] }

theorem u2108 : Upper (D 5) (R 5) [6,24,192,33,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2108
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2109 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 196, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 196 42 273 33 108 172 300), lower := (rows 7 26 196 42 273 33 64 128 256), losses := [] }

theorem u2109 : Upper (D 5) (R 5) [6,24,192,34,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2109
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2110 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 196 42 273 36 105 169 297), lower := (rows 7 26 196 42 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 25 16 37 64 128 256), good := (rows 46 26 228 42 314 36 64 128 256) }] }

theorem u2110 : Upper (D 5) (R 5) [6,24,192,34,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2110
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2111 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 42 273 40 101 165 293), lower := (rows 7 26 196 42 273 40 64 128 256), losses := [] }

theorem u2111 : Upper (D 5) (R 5) [6,24,192,34,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2111
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2112 : Route 9 := (fun mask => (mask,id))

def c2112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2112 : Upper (D 5) (R 5) [6,24,192,34,260,1] 13 := by
  apply FastRouting.sound _ _ [6,24,192,34,260,1] 13 (by decide) (choices 1) [1,8,32] r2112 c2112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u366
  · exact u367
  · exact u368

def b2113 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 42 276 40 97 161 289), lower := (rows 7 26 196 42 276 40 64 128 256), losses := [] }

theorem u2113 : Upper (D 5) (R 5) [6,24,192,34,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2113
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2114 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(3,1),(4,2)], upper := (rows 7 26 196 44 273 33 106 170 298), lower := (rows 7 26 196 44 273 33 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 17 49 66 130 258), good := (rows 499 506 192 40 305 49 64 128 256) }] }

theorem u2114 : Upper (D 5) (R 5) [6,24,192,36,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2114
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2115 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 196 44 273 34 105 169 297), lower := (rows 7 26 196 44 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 9 16 51 64 128 256), good := (rows 46 58 196 44 314 34 64 128 256) }] }

theorem u2115 : Upper (D 5) (R 5) [6,24,192,36,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2115
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2116 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 26 196 44 273 40 99 163 291), lower := (rows 7 26 196 44 273 40 64 128 256), losses := [] }

theorem u2116 : Upper (D 5) (R 5) [6,24,192,36,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2116
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2117 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 196 265 49 34 108 172 300), lower := (rows 7 26 196 265 49 34 64 128 256), losses := [] }

theorem u2117 : Upper (D 5) (R 5) [6,24,192,257,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2117
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2118 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 196 265 49 36 106 170 298), lower := (rows 7 26 196 265 49 36 64 128 256), losses := [] }

theorem u2118 : Upper (D 5) (R 5) [6,24,192,257,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2118
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2119 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 50, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 26 196 265 49 40 102 166 294), lower := (rows 7 26 196 265 49 40 64 128 256), losses := [] }

theorem u2119 : Upper (D 5) (R 5) [6,24,192,257,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2119
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2120 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 196 265 52 33 106 170 298), lower := (rows 7 26 196 265 52 33 64 128 256), losses := [] }

theorem u2120 : Upper (D 5) (R 5) [6,24,192,257,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2120
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2121 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2),(4,0)], upper := (rows 7 26 196 265 52 34 105 169 297), lower := (rows 7 26 196 265 52 34 64 128 256), losses := [] }

theorem u2121 : Upper (D 5) (R 5) [6,24,192,257,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2121
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2122 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(1,0),(3,2)], upper := (rows 7 26 196 265 52 40 99 163 291), lower := (rows 7 26 196 265 52 40 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 42 64 128 256), good := (rows 54 58 196 314 52 42 64 128 256) }] }

theorem u2122 : Upper (D 5) (R 5) [6,24,192,257,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2122
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2123 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 26 196 266 49 33 108 172 300), lower := (rows 7 26 196 266 49 33 64 128 256), losses := [] }

theorem u2123 : Upper (D 5) (R 5) [6,24,192,258,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2123
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2124 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 196 266 49 36 105 169 297), lower := (rows 7 26 196 266 49 36 64 128 256), losses := [] }

theorem u2124 : Upper (D 5) (R 5) [6,24,192,258,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2124
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2125 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 196, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 196 266 49 40 101 165 293), lower := (rows 7 26 196 266 49 40 64 128 256), losses := [] }

theorem u2125 : Upper (D 5) (R 5) [6,24,192,258,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2125
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2126 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 196 266 52 33 105 169 297), lower := (rows 7 26 196 266 52 33 64 128 256), losses := [] }

theorem u2126 : Upper (D 5) (R 5) [6,24,192,258,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2126
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2127 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2),(4,0)], upper := (rows 7 26 196 266 52 40 97 161 289), lower := (rows 7 26 196 266 52 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 42 64 128 256), good := (rows 54 58 196 298 52 40 64 128 256) }] }

theorem u2127 : Upper (D 5) (R 5) [6,24,192,258,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2127
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2128 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 26 196 268 49 33 106 170 298), lower := (rows 7 26 196 268 49 33 64 128 256), losses := [] }

theorem u2128 : Upper (D 5) (R 5) [6,24,192,260,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2128
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2129 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 196 268 49 34 105 169 297), lower := (rows 7 26 196 268 49 34 64 128 256), losses := [] }

theorem u2129 : Upper (D 5) (R 5) [6,24,192,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2129
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2130 : PairBound 9 := { available := 35, camps := [], pairs := [(4,1),(4,2)], upper := (rows 7 26 196 268 49 40 99 163 291), lower := (rows 7 26 196 268 49 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 42 64 128 256), good := (rows 53 56 196 300 49 40 64 128 256) },{ target := 2, region := (rows 1 2 0 8 17 42 65 129 257), good := (rows 499 58 192 296 497 40 64 128 256) }] }

theorem u2130 : Upper (D 5) (R 5) [6,24,192,260,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2130
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2131 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 25 148 34 360 424 296), lower := (rows 7 35 76 25 148 34 64 128 256), losses := [] }

theorem u2131 : Upper (D 5) (R 5) [6,33,72,17,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2131
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2132 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 35 76 25 148 40 354 418 290), lower := (rows 7 35 76 25 148 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 25 44 67 131 259), good := (rows 502 498 124 508 180 60 64 128 256) }] }

theorem u2132 : Upper (D 5) (R 5) [6,33,72,17,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2132
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2133 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 290, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 25 148 288 106 170 298), lower := (rows 7 35 76 25 148 288 64 128 256), losses := [] }

theorem u2133 : Upper (D 5) (R 5) [6,33,72,17,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2133
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2134 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 25 176 34 332 396 268), lower := (rows 7 35 76 25 176 34 64 128 256), losses := [] }

theorem u2134 : Upper (D 5) (R 5) [6,33,72,17,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2134
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2135 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 25 176 36 330 394 266), lower := (rows 7 35 76 25 176 36 64 128 256), losses := [] }

theorem u2135 : Upper (D 5) (R 5) [6,33,72,17,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2135
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2136 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 35 76 25 176 40 326 390 262), lower := (rows 7 35 76 25 176 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 44 65 129 257), good := (rows 502 498 124 508 176 60 64 128 256) }] }

theorem u2136 : Upper (D 5) (R 5) [6,33,72,17,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2136
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2137 : Route 9 := (fun mask => (mask,id))

def c2137 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2137 : Upper (D 5) (R 5) [6,33,72,17,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,160,256] 13 (by decide) (choices 1) [2,4,8] r2137 c2137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u369
  · exact u370
  · exact u371

def b2138 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 25 400 34 108 172 300), lower := (rows 7 35 76 25 400 34 64 128 256), losses := [] }

theorem u2138 : Upper (D 5) (R 5) [6,33,72,17,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2138
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2139 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 25 400 36 106 170 298), lower := (rows 7 35 76 25 400 36 64 128 256), losses := [] }

theorem u2139 : Upper (D 5) (R 5) [6,33,72,17,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2139
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2140 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 35 76 25 400 40 102 166 294), lower := (rows 7 35 76 25 400 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 44 65 129 257), good := (rows 502 498 124 508 400 60 64 128 256) }] }

theorem u2140 : Upper (D 5) (R 5) [6,33,72,17,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2140
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2141 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 26 148 33 360 424 296), lower := (rows 7 35 76 26 148 33 64 128 256), losses := [] }

theorem u2141 : Upper (D 5) (R 5) [6,33,72,18,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2141
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2142 : PairBound 9 := { available := 289, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 35 76 26 148 40 353 417 289), lower := (rows 7 35 76 26 148 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 44 67 131 259), good := (rows 501 497 124 508 180 60 64 128 256) }] }

theorem u2142 : Upper (D 5) (R 5) [6,33,72,18,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2142
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2143 : Route 9 := (fun mask => (mask,id))

def c2143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2143 : Upper (D 5) (R 5) [6,33,72,18,132,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,132,256] 13 (by decide) (choices 1) [1,8,32] r2143 c2143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u372
  · exact u373
  · exact u374

def b2144 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 26 400 33 108 172 300), lower := (rows 7 35 76 26 400 33 64 128 256), losses := [] }

theorem u2144 : Upper (D 5) (R 5) [6,33,72,18,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2144
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2145 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 26 400 36 105 169 297), lower := (rows 7 35 76 26 400 36 64 128 256), losses := [] }

theorem u2145 : Upper (D 5) (R 5) [6,33,72,18,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2145
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2146 : PairBound 9 := { available := 37, camps := [], pairs := [(1,2),(4,1)], upper := (rows 7 35 76 26 400 40 101 165 293), lower := (rows 7 35 76 26 400 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 19 44 65 129 257), good := (rows 501 497 108 56 400 40 64 128 256) },{ target := 2, region := (rows 1 3 0 8 16 44 64 128 256), good := (rows 35 35 104 58 400 40 64 128 256) }] }

theorem u2146 : Upper (D 5) (R 5) [6,33,72,18,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2146
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2147 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 28 145 34 360 424 296), lower := (rows 7 35 76 28 145 34 64 128 256), losses := [] }

theorem u2147 : Upper (D 5) (R 5) [6,33,72,20,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2147
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2148 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 400, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 28 145 40 354 418 290), lower := (rows 7 35 76 28 145 40 64 128 256), losses := [] }

theorem u2148 : Upper (D 5) (R 5) [6,33,72,20,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2148
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2149 : Route 9 := (fun mask => (mask,id))

def c2149 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2149 : Upper (D 5) (R 5) [6,33,72,20,129,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20,129,256] 13 (by decide) (choices 1) [2,8,32] r2149 c2149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u375
  · exact u376
  · exact u377

def b2150 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 28 146 33 360 424 296), lower := (rows 7 35 76 28 146 33 64 128 256), losses := [] }

theorem u2150 : Upper (D 5) (R 5) [6,33,72,20,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2150
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2151 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 400, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 28 146 40 353 417 289), lower := (rows 7 35 76 28 146 40 64 128 256), losses := [] }

theorem u2151 : Upper (D 5) (R 5) [6,33,72,20,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2151
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2152 : Route 9 := (fun mask => (mask,id))

def c2152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2152 : Upper (D 5) (R 5) [6,33,72,20,130,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20,130,256] 13 (by decide) (choices 1) [1,8,32] r2152 c2152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u378
  · exact u379
  · exact u380

def b2153 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 28 176 33 330 394 266), lower := (rows 7 35 76 28 176 33 64 128 256), losses := [] }

theorem u2153 : Upper (D 5) (R 5) [6,33,72,20,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2153
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2154 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 28 176 34 329 393 265), lower := (rows 7 35 76 28 176 34 64 128 256), losses := [] }

theorem u2154 : Upper (D 5) (R 5) [6,33,72,20,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2154
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2155 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 400, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 28 176 40 323 387 259), lower := (rows 7 35 76 28 176 40 64 128 256), losses := [] }

theorem u2155 : Upper (D 5) (R 5) [6,33,72,20,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2155
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2156 : Route 9 := (fun mask => (mask,id))

def c2156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2156 : Upper (D 5) (R 5) [6,33,72,20,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20,160,256] 13 (by decide) (choices 1) [1,2,8] r2156 c2156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u381
  · exact u382
  · exact u383

def b2157 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 28 400 33 106 170 298), lower := (rows 7 35 76 28 400 33 64 128 256), losses := [] }

theorem u2157 : Upper (D 5) (R 5) [6,33,72,20,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2157
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2158 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 28 400 34 105 169 297), lower := (rows 7 35 76 28 400 34 64 128 256), losses := [] }

theorem u2158 : Upper (D 5) (R 5) [6,33,72,20,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2158
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2159 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 400, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 28 400 40 99 163 291), lower := (rows 7 35 76 28 400 40 64 128 256), losses := [] }

theorem u2159 : Upper (D 5) (R 5) [6,33,72,20,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2159
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2159
end Delivery.IrregularNine14.P05
