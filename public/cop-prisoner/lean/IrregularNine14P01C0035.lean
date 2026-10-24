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

def b2100 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 292 200 18 240 240 240 496), lower := (rows 23 11 292 200 18 32 64 128 256), losses := [] }

theorem u2100 : Upper (D 1) (R 1) [22,9,288,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2100
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2101 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 23 11 292 200 48 242 210 210 466), lower := (rows 23 11 292 200 48 32 64 128 256), losses := [] }

theorem u2101 : Upper (D 1) (R 1) [22,9,288,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2101
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2102 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 23 11 292 200 80 178 242 178 434), lower := (rows 23 11 292 200 80 32 64 128 256), losses := [] }

theorem u2102 : Upper (D 1) (R 1) [22,9,288,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2102
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2103 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 76 168 18 496 464 464 464), lower := (rows 23 35 76 168 18 32 64 128 256), losses := [] }

theorem u2103 : Upper (D 1) (R 1) [22,33,72,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2103
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2104 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 76 168 80 434 466 402 402), lower := (rows 23 35 76 168 80 32 64 128 256), losses := [] }

theorem u2104 : Upper (D 1) (R 1) [22,33,72,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2104
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2105 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 23 35 76 168 144 370 338 466 338), lower := (rows 23 35 76 168 144 32 64 128 256), losses := [] }

theorem u2105 : Upper (D 1) (R 1) [22,33,72,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2105
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2106 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 35 76 168 272 242 210 210 466), lower := (rows 23 35 76 168 272 32 64 128 256), losses := [] }

theorem u2106 : Upper (D 1) (R 1) [22,33,72,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2106
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2107 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 76 296 18 240 208 208 464), lower := (rows 23 35 76 296 18 32 64 128 256), losses := [] }

theorem u2107 : Upper (D 1) (R 1) [22,33,72,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2107
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2108 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 76 296 80 178 210 146 402), lower := (rows 23 35 76 296 80 32 64 128 256), losses := [] }

theorem u2108 : Upper (D 1) (R 1) [22,33,72,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2108
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2109 : Route 9 := (fun mask => (mask,id))

def c2109 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2109 : Upper (D 1) (R 1) [22,33,72,288,128] 13 := by
  apply FastRouting.sound _ _ [22,33,72,288,128] 13 (by decide) (choices 1) [2,16,64,128] r2109 c2109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u382
  · exact u383
  · exact u384
  · exact u385

def b2110 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 76 392 18 240 240 240 496), lower := (rows 23 35 76 392 18 32 64 128 256), losses := [] }

theorem u2110 : Upper (D 1) (R 1) [22,33,72,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2110
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2111 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 76 392 48 242 210 210 466), lower := (rows 23 35 76 392 48 32 64 128 256), losses := [] }

theorem u2111 : Upper (D 1) (R 1) [22,33,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2111
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2112 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 76 392 80 178 242 178 434), lower := (rows 23 35 76 392 80 32 64 128 256), losses := [] }

theorem u2112 : Upper (D 1) (R 1) [22,33,72,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2112
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2113 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 23 35 76 392 144 114 114 242 370), lower := (rows 23 35 76 392 144 32 64 128 256), losses := [] }

theorem u2113 : Upper (D 1) (R 1) [22,33,72,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2113
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2114 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 196 56 18 488 456 456 456), lower := (rows 23 35 196 56 18 32 64 128 256), losses := [] }

theorem u2114 : Upper (D 1) (R 1) [22,33,192,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2114
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2115 : PairBound 9 := { available := 450, camps := [], pairs := [], upper := (rows 23 35 196 56 24 482 450 450 450), lower := (rows 23 35 196 56 24 32 64 128 256), losses := [] }

theorem u2115 : Upper (D 1) (R 1) [22,33,192,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2115
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2116 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 196 56 80 426 458 394 394), lower := (rows 23 35 196 56 80 32 64 128 256), losses := [] }

theorem u2116 : Upper (D 1) (R 1) [22,33,192,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2116
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2117 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 23 35 196 56 272 234 202 202 458), lower := (rows 23 35 196 56 272 32 64 128 256), losses := [] }

theorem u2117 : Upper (D 1) (R 1) [22,33,192,48,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2117
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2118 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 196 88 18 424 488 424 424), lower := (rows 23 35 196 88 18 32 64 128 256), losses := [] }

theorem u2118 : Upper (D 1) (R 1) [22,33,192,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2118
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2119 : PairBound 9 := { available := 418, camps := [], pairs := [], upper := (rows 23 35 196 88 24 418 482 418 418), lower := (rows 23 35 196 88 24 32 64 128 256), losses := [] }

theorem u2119 : Upper (D 1) (R 1) [22,33,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2119
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2120 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 196 88 48 426 458 394 394), lower := (rows 23 35 196 88 48 32 64 128 256), losses := [] }

theorem u2120 : Upper (D 1) (R 1) [22,33,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2120
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2121 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 35 196 88 144 298 362 426 298), lower := (rows 23 35 196 88 144 32 64 128 256), losses := [] }

theorem u2121 : Upper (D 1) (R 1) [22,33,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2121
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2122 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 23 35 196 88 272 170 234 170 426), lower := (rows 23 35 196 88 272 32 64 128 256), losses := [] }

theorem u2122 : Upper (D 1) (R 1) [22,33,192,80,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2122
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2123 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 196 104 18 440 472 408 408), lower := (rows 23 35 196 104 18 32 64 128 256), losses := [] }

theorem u2123 : Upper (D 1) (R 1) [22,33,192,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2123
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2124 : PairBound 9 := { available := 402, camps := [], pairs := [], upper := (rows 23 35 196 104 24 434 466 402 402), lower := (rows 23 35 196 104 24 32 64 128 256), losses := [] }

theorem u2124 : Upper (D 1) (R 1) [22,33,192,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2124
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2125 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 35 196 104 144 314 346 410 282), lower := (rows 23 35 196 104 144 32 64 128 256), losses := [] }

theorem u2125 : Upper (D 1) (R 1) [22,33,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2125
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2126 : PairBound 9 := { available := 154, camps := [], pairs := [], upper := (rows 23 35 196 104 272 186 218 154 410), lower := (rows 23 35 196 104 272 32 64 128 256), losses := [] }

theorem u2126 : Upper (D 1) (R 1) [22,33,192,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2126
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2127 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 196 280 18 232 232 232 488), lower := (rows 23 35 196 280 18 32 64 128 256), losses := [] }

theorem u2127 : Upper (D 1) (R 1) [22,33,192,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2127
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2128 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 23 35 196 280 24 226 226 226 482), lower := (rows 23 35 196 280 24 32 64 128 256), losses := [] }

theorem u2128 : Upper (D 1) (R 1) [22,33,192,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2128
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2129 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 196 280 48 234 202 202 458), lower := (rows 23 35 196 280 48 32 64 128 256), losses := [] }

theorem u2129 : Upper (D 1) (R 1) [22,33,192,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2129
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2130 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 196 280 80 170 234 170 426), lower := (rows 23 35 196 280 80 32 64 128 256), losses := [] }

theorem u2130 : Upper (D 1) (R 1) [22,33,192,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2130
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2131 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 196 296 18 248 216 216 472), lower := (rows 23 35 196 296 18 32 64 128 256), losses := [] }

theorem u2131 : Upper (D 1) (R 1) [22,33,192,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2131
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2132 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 35 196 296 24 242 210 210 466), lower := (rows 23 35 196 296 24 32 64 128 256), losses := [] }

theorem u2132 : Upper (D 1) (R 1) [22,33,192,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2132
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2133 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 196 296 80 186 218 154 410), lower := (rows 23 35 196 296 80 32 64 128 256), losses := [] }

theorem u2133 : Upper (D 1) (R 1) [22,33,192,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2133
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2134 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 196 328 18 184 248 184 440), lower := (rows 23 35 196 328 18 32 64 128 256), losses := [] }

theorem u2134 : Upper (D 1) (R 1) [22,33,192,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2134
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2135 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 23 35 196 328 24 178 242 178 434), lower := (rows 23 35 196 328 24 32 64 128 256), losses := [] }

theorem u2135 : Upper (D 1) (R 1) [22,33,192,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2135
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2136 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 196 328 48 186 218 154 410), lower := (rows 23 35 196 328 48 32 64 128 256), losses := [] }

theorem u2136 : Upper (D 1) (R 1) [22,33,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2136
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2137 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 35 196 328 144 58 122 186 314), lower := (rows 23 35 196 328 144 32 64 128 256), losses := [] }

theorem u2137 : Upper (D 1) (R 1) [22,33,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2137
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2138 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 268 104 18 240 208 208 464), lower := (rows 23 35 268 104 18 32 64 128 256), losses := [] }

theorem u2138 : Upper (D 1) (R 1) [22,33,264,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2138
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2139 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 268 104 80 178 210 146 402), lower := (rows 23 35 268 104 80 32 64 128 256), losses := [] }

theorem u2139 : Upper (D 1) (R 1) [22,33,264,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2139
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2140 : Route 9 := (fun mask => (mask,id))

def c2140 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2140 : Upper (D 1) (R 1) [22,33,264,96,128] 13 := by
  apply FastRouting.sound _ _ [22,33,264,96,128] 13 (by decide) (choices 1) [2,16,64,128] r2140 c2140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u386
  · exact u387
  · exact u388
  · exact u389

def b2141 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 268 200 18 240 240 240 496), lower := (rows 23 35 268 200 18 32 64 128 256), losses := [] }

theorem u2141 : Upper (D 1) (R 1) [22,33,264,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2141
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2142 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 268 200 48 242 210 210 466), lower := (rows 23 35 268 200 48 32 64 128 256), losses := [] }

theorem u2142 : Upper (D 1) (R 1) [22,33,264,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2142
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2143 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 268 200 80 178 242 178 434), lower := (rows 23 35 268 200 80 32 64 128 256), losses := [] }

theorem u2143 : Upper (D 1) (R 1) [22,33,264,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2143
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2144 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 324 56 18 232 200 200 456), lower := (rows 23 35 324 56 18 32 64 128 256), losses := [] }

theorem u2144 : Upper (D 1) (R 1) [22,33,320,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2144
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2145 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 23 35 324 56 24 226 194 194 450), lower := (rows 23 35 324 56 24 32 64 128 256), losses := [] }

theorem u2145 : Upper (D 1) (R 1) [22,33,320,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2145
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2146 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 56 80 170 202 138 394), lower := (rows 23 35 324 56 80 32 64 128 256), losses := [] }

theorem u2146 : Upper (D 1) (R 1) [22,33,320,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2146
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2147 : Route 9 := (fun mask => (mask,id))

def c2147 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2147 : Upper (D 1) (R 1) [22,33,320,48,128] 13 := by
  apply FastRouting.sound _ _ [22,33,320,48,128] 13 (by decide) (choices 1) [2,8,64,128] r2147 c2147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u390
  · exact u391
  · exact u392
  · exact u393

def b2148 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 324 88 18 168 232 168 424), lower := (rows 23 35 324 88 18 32 64 128 256), losses := [] }

theorem u2148 : Upper (D 1) (R 1) [22,33,320,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2148
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2149 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 23 35 324 88 24 162 226 162 418), lower := (rows 23 35 324 88 24 32 64 128 256), losses := [] }

theorem u2149 : Upper (D 1) (R 1) [22,33,320,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2149
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2150 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 324 88 48 170 202 138 394), lower := (rows 23 35 324 88 48 32 64 128 256), losses := [] }

theorem u2150 : Upper (D 1) (R 1) [22,33,320,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2150
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2151 : Route 9 := (fun mask => (mask,id))

def c2151 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2151 : Upper (D 1) (R 1) [22,33,320,80,128] 13 := by
  apply FastRouting.sound _ _ [22,33,320,80,128] 13 (by decide) (choices 1) [2,8,128] r2151 c2151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u394
  · exact u395
  · exact u396

def b2152 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 324 104 18 184 216 152 408), lower := (rows 23 35 324 104 18 32 64 128 256), losses := [] }

theorem u2152 : Upper (D 1) (R 1) [22,33,320,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2152
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2153 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 23 35 324 104 24 178 210 146 402), lower := (rows 23 35 324 104 24 32 64 128 256), losses := [] }

theorem u2153 : Upper (D 1) (R 1) [22,33,320,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2153
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2154 : Route 9 := (fun mask => (mask,id))

def c2154 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2154 : Upper (D 1) (R 1) [22,33,320,96,128] 13 := by
  apply FastRouting.sound _ _ [22,33,320,96,128] 13 (by decide) (choices 1) [2,8,16,128] r2154 c2154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u397
  · exact u398
  · exact u399
  · exact u400

def b2155 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 324 152 18 232 232 232 488), lower := (rows 23 35 324 152 18 32 64 128 256), losses := [] }

theorem u2155 : Upper (D 1) (R 1) [22,33,320,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2155
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2156 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 23 35 324 152 24 226 226 226 482), lower := (rows 23 35 324 152 24 32 64 128 256), losses := [] }

theorem u2156 : Upper (D 1) (R 1) [22,33,320,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2156
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2157 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 324 152 48 234 202 202 458), lower := (rows 23 35 324 152 48 32 64 128 256), losses := [] }

theorem u2157 : Upper (D 1) (R 1) [22,33,320,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2157
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2158 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 152 80 170 234 170 426), lower := (rows 23 35 324 152 80 32 64 128 256), losses := [] }

theorem u2158 : Upper (D 1) (R 1) [22,33,320,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2158
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2159 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 23 35 324 152 144 106 106 234 362), lower := (rows 23 35 324 152 144 32 64 128 256), losses := [] }

theorem u2159 : Upper (D 1) (R 1) [22,33,320,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2159
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2159
end Delivery.IrregularNine14.P01
