import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0005
import IrregularNine14P03C0006

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2100 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 26 145 33 224 224 480), lower := (rows 289 7 76 26 145 33 64 128 256), losses := [] }

theorem u2100 : Upper (D 3) (R 3) [288,5,72,18,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2100
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2101 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 26 145 96 225 161 417), lower := (rows 289 7 76 26 145 96 64 128 256), losses := [] }

theorem u2101 : Upper (D 3) (R 3) [288,5,72,18,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2101
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2102 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 26 145 160 97 225 353), lower := (rows 289 7 76 26 145 160 64 128 256), losses := [] }

theorem u2102 : Upper (D 3) (R 3) [288,5,72,18,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2102
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2103 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 76 137 50 33 208 208 464), lower := (rows 289 7 76 137 50 33 64 128 256), losses := [] }

theorem u2103 : Upper (D 3) (R 3) [288,5,72,129,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2103
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2104 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 76 137 50 48 193 193 449), lower := (rows 289 7 76 137 50 48 64 128 256), losses := [] }

theorem u2104 : Upper (D 3) (R 3) [288,5,72,129,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2104
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2105 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 137 50 96 209 145 401), lower := (rows 289 7 76 137 50 96 64 128 256), losses := [] }

theorem u2105 : Upper (D 3) (R 3) [288,5,72,129,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2105
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2106 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 137 50 160 81 209 337), lower := (rows 289 7 76 137 50 160 64 128 256), losses := [] }

theorem u2106 : Upper (D 3) (R 3) [288,5,72,129,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2106
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2107 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 289 7 76 137 81 34 240 176 432), lower := (rows 289 7 76 137 81 34 64 128 256), losses := [] }

theorem u2107 : Upper (D 3) (R 3) [288,5,72,129,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2107
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2108 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 289 7 76 137 81 48 226 162 418), lower := (rows 289 7 76 137 81 48 64 128 256), losses := [] }

theorem u2108 : Upper (D 3) (R 3) [288,5,72,129,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2108
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2109 : Route 9 := (fun mask => (mask,id))

def c2109 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2109 : Upper (D 3) (R 3) [288,5,72,129,65,128] 13 := by
  apply FastRouting.sound _ _ [288,5,72,129,65,128] 13 (by decide) (choices 1) [2,16,32] r2109 c2109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u347
  · exact u348
  · exact u349

def b2110 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 137 112 33 210 146 402), lower := (rows 289 7 76 137 112 33 64 128 256), losses := [] }

theorem u2110 : Upper (D 3) (R 3) [288,5,72,129,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2110
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2111 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 7 76 137 112 34 209 145 401), lower := (rows 289 7 76 137 112 34 64 128 256), losses := [] }

theorem u2111 : Upper (D 3) (R 3) [288,5,72,129,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2111
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2112 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 7 76 137 112 48 195 131 387), lower := (rows 289 7 76 137 112 48 64 128 256), losses := [] }

theorem u2112 : Upper (D 3) (R 3) [288,5,72,129,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2112
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2113 : PairBound 9 := { available := 19, camps := [], pairs := [(4,0)], upper := (rows 289 7 76 137 112 160 83 147 275), lower := (rows 289 7 76 137 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 288 22 124 168 112 160 64 160 256) }] }

theorem u2113 : Upper (D 3) (R 3) [288,5,72,129,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2113
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2114 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 137 176 33 82 210 338), lower := (rows 289 7 76 137 176 33 64 128 256), losses := [] }

theorem u2114 : Upper (D 3) (R 3) [288,5,72,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2114
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2115 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 289 7 76 137 176 34 81 209 337), lower := (rows 289 7 76 137 176 34 64 128 256), losses := [] }

theorem u2115 : Upper (D 3) (R 3) [288,5,72,129,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2115
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2116 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 289 7 76 137 176 48 67 195 323), lower := (rows 289 7 76 137 176 48 64 128 256), losses := [] }

theorem u2116 : Upper (D 3) (R 3) [288,5,72,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2116
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2117 : Route 9 := (fun mask => (mask,id))

def c2117 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2117 : Upper (D 3) (R 3) [288,5,72,129,160,64] 13 := by
  apply FastRouting.sound _ _ [288,5,72,129,160,64] 13 (by decide) (choices 1) [1,2,16] r2117 c2117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u350
  · exact u351
  · exact u352

def b2118 : PairBound 9 := { available := 50, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 137 208 33 114 178 306), lower := (rows 289 7 76 137 208 33 64 128 256), losses := [] }

theorem u2118 : Upper (D 3) (R 3) [288,5,72,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2118
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2119 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 7 76 137 208 34 113 177 305), lower := (rows 289 7 76 137 208 34 64 128 256), losses := [] }

theorem u2119 : Upper (D 3) (R 3) [288,5,72,129,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2119
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2120 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 289 7 76 137 208 48 99 163 291), lower := (rows 289 7 76 137 208 48 64 128 256), losses := [] }

theorem u2120 : Upper (D 3) (R 3) [288,5,72,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2120
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2121 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 196 42 81 33 216 152 408), lower := (rows 289 7 196 42 81 33 64 128 256), losses := [] }

theorem u2121 : Upper (D 3) (R 3) [288,5,192,34,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2121
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2122 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 7 196 42 81 40 209 145 401), lower := (rows 289 7 196 42 81 40 64 128 256), losses := [] }

theorem u2122 : Upper (D 3) (R 3) [288,5,192,34,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2122
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2123 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 289 7 196 42 81 48 201 137 393), lower := (rows 289 7 196 42 81 48 64 128 256), losses := [] }

theorem u2123 : Upper (D 3) (R 3) [288,5,192,34,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2123
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2124 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 196 42 81 160 89 153 281), lower := (rows 289 7 196 42 81 160 64 128 256), losses := [] }

theorem u2124 : Upper (D 3) (R 3) [288,5,192,34,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2124
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2125 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 196 56 81 33 202 138 394), lower := (rows 289 7 196 56 81 33 64 128 256), losses := [] }

theorem u2125 : Upper (D 3) (R 3) [288,5,192,48,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2125
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2126 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 289 7 196 56 81 34 201 137 393), lower := (rows 289 7 196 56 81 34 64 128 256), losses := [] }

theorem u2126 : Upper (D 3) (R 3) [288,5,192,48,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2126
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2127 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 7 196 56 81 40 195 131 387), lower := (rows 289 7 196 56 81 40 64 128 256), losses := [] }

theorem u2127 : Upper (D 3) (R 3) [288,5,192,48,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2127
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2128 : Route 9 := (fun mask => (mask,id))

def c2128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2128 : Upper (D 3) (R 3) [288,5,192,48,65,128] 13 := by
  apply FastRouting.sound _ _ [288,5,192,48,65,128] 13 (by decide) (choices 1) [1,2,8] r2128 c2128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u353
  · exact u354
  · exact u355

def b2129 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 289 7 196 73 145 34 120 184 312), lower := (rows 289 7 196 73 145 34 64 128 256), losses := [] }

theorem u2129 : Upper (D 3) (R 3) [288,5,192,65,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2129
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2130 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 289 7 196 73 145 40 114 178 306), lower := (rows 289 7 196 73 145 40 64 128 256), losses := [] }

theorem u2130 : Upper (D 3) (R 3) [288,5,192,65,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2130
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2131 : PairBound 9 := { available := 50, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 73 152 33 114 178 306), lower := (rows 289 7 196 73 152 33 64 128 256), losses := [] }

theorem u2131 : Upper (D 3) (R 3) [288,5,192,65,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2131
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2132 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 7 196 73 152 34 113 177 305), lower := (rows 289 7 196 73 152 34 64 128 256), losses := [] }

theorem u2132 : Upper (D 3) (R 3) [288,5,192,65,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2132
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2133 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 289 7 196 73 152 48 99 163 291), lower := (rows 289 7 196 73 152 48 64 128 256), losses := [] }

theorem u2133 : Upper (D 3) (R 3) [288,5,192,65,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2133
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2134 : PairBound 9 := { available := 26, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 73 176 33 90 154 282), lower := (rows 289 7 196 73 176 33 64 128 256), losses := [] }

theorem u2134 : Upper (D 3) (R 3) [288,5,192,65,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2134
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2135 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 289 7 196 73 176 34 89 153 281), lower := (rows 289 7 196 73 176 34 64 128 256), losses := [] }

theorem u2135 : Upper (D 3) (R 3) [288,5,192,65,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2135
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2136 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 289 7 196 73 176 40 83 147 275), lower := (rows 289 7 196 73 176 40 64 128 256), losses := [] }

theorem u2136 : Upper (D 3) (R 3) [288,5,192,65,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2136
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2137 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 289 7 196 73 176 48 75 139 267), lower := (rows 289 7 196 73 176 48 64 128 256), losses := [] }

theorem u2137 : Upper (D 3) (R 3) [288,5,192,65,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2137
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2138 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 88 176 33 75 139 267), lower := (rows 289 7 196 88 176 33 64 128 256), losses := [] }

theorem u2138 : Upper (D 3) (R 3) [288,5,192,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2138
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2139 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 289 7 196 88 176 34 73 137 265), lower := (rows 289 7 196 88 176 34 64 128 256), losses := [] }

theorem u2139 : Upper (D 3) (R 3) [288,5,192,80,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2139
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2140 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 7 196 88 176 40 67 131 259), lower := (rows 289 7 196 88 176 40 64 128 256), losses := [] }

theorem u2140 : Upper (D 3) (R 3) [288,5,192,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2140
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2141 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 22 73 145 33 224 224 480), lower := (rows 289 14 22 73 145 33 64 128 256), losses := [] }

theorem u2141 : Upper (D 3) (R 3) [288,12,18,65,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2141
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2142 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 22 73 145 96 225 161 417), lower := (rows 289 14 22 73 145 96 64 128 256), losses := [] }

theorem u2142 : Upper (D 3) (R 3) [288,12,18,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2142
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2143 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 52 73 145 33 194 194 450), lower := (rows 289 14 52 73 145 33 64 128 256), losses := [] }

theorem u2143 : Upper (D 3) (R 3) [288,12,48,65,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2143
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2144 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 14 52 73 145 34 193 193 449), lower := (rows 289 14 52 73 145 34 64 128 256), losses := [] }

theorem u2144 : Upper (D 3) (R 3) [288,12,48,65,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2144
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2145 : Route 9 := (fun mask => (mask,id))

def c2145 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2145 : Upper (D 3) (R 3) [288,12,48,65,129,64] 13 := by
  apply FastRouting.sound _ _ [288,12,48,65,129,64] 13 (by decide) (choices 1) [1,2,128] r2145 c2145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u356
  · exact u357
  · exact u358

def b2146 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 52 73 145 160 67 195 323), lower := (rows 289 14 52 73 145 160 64 128 256), losses := [] }

theorem u2146 : Upper (D 3) (R 3) [288,12,48,65,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2146
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2147 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 137 50 33 208 208 464), lower := (rows 289 14 69 137 50 33 64 128 256), losses := [] }

theorem u2147 : Upper (D 3) (R 3) [288,12,65,129,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2147
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2148 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 14 69 137 50 48 193 193 449), lower := (rows 289 14 69 137 50 48 64 128 256), losses := [] }

theorem u2148 : Upper (D 3) (R 3) [288,12,65,129,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2148
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2149 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 137 50 96 209 145 401), lower := (rows 289 14 69 137 50 96 64 128 256), losses := [] }

theorem u2149 : Upper (D 3) (R 3) [288,12,65,129,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2149
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2150 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 137 112 33 210 146 402), lower := (rows 289 14 69 137 112 33 64 128 256), losses := [] }

theorem u2150 : Upper (D 3) (R 3) [288,12,65,129,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2150
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2151 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 14 69 137 112 34 209 145 401), lower := (rows 289 14 69 137 112 34 64 128 256), losses := [] }

theorem u2151 : Upper (D 3) (R 3) [288,12,65,129,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2151
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2152 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 14 69 137 112 48 195 131 387), lower := (rows 289 14 69 137 112 48 64 128 256), losses := [] }

theorem u2152 : Upper (D 3) (R 3) [288,12,65,129,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2152
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2153 : Route 9 := (fun mask => (mask,id))

def c2153 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2153 : Upper (D 3) (R 3) [288,12,65,129,96,128] 13 := by
  apply FastRouting.sound _ _ [288,12,65,129,96,128] 13 (by decide) (choices 1) [1,2,16] r2153 c2153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u359
  · exact u360
  · exact u361

def b2154 : PairBound 9 := { available := 50, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 137 208 33 114 178 306), lower := (rows 289 14 69 137 208 33 64 128 256), losses := [] }

theorem u2154 : Upper (D 3) (R 3) [288,12,65,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2154
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2155 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 14 69 137 208 34 113 177 305), lower := (rows 289 14 69 137 208 34 64 128 256), losses := [] }

theorem u2155 : Upper (D 3) (R 3) [288,12,65,129,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2155
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2156 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 289 14 69 137 208 48 99 163 291), lower := (rows 289 14 69 137 208 48 64 128 256), losses := [] }

theorem u2156 : Upper (D 3) (R 3) [288,12,65,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2156
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2157 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 168 145 33 82 210 338), lower := (rows 289 14 69 168 145 33 64 128 256), losses := [] }

theorem u2157 : Upper (D 3) (R 3) [288,12,65,160,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2157
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2158 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 289 14 69 168 145 34 81 209 337), lower := (rows 289 14 69 168 145 34 64 128 256), losses := [] }

theorem u2158 : Upper (D 3) (R 3) [288,12,65,160,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2158
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2159 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 289 14 69 168 145 48 67 195 323), lower := (rows 289 14 69 168 145 48 64 128 256), losses := [] }

theorem u2159 : Upper (D 3) (R 3) [288,12,65,160,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2159
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2159
end Delivery.IrregularNine14.P03
