import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0001

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2100 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 22 164 265 81 96 68 162 290), lower := (rows 11 22 164 265 81 96 68 128 256), losses := [] }

theorem u2100 : Upper (D 6) (R 6) [10,20,160,257,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2101 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 265, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 164 265 81 96 96 134 262), lower := (rows 11 22 164 265 81 96 96 128 256), losses := [] }

theorem u2101 : Upper (D 6) (R 6) [10,20,160,257,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2102 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 150, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 265 82 96 65 164 292), lower := (rows 11 22 164 265 82 96 65 128 256), losses := [] }

theorem u2102 : Upper (D 6) (R 6) [10,20,160,257,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2103 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 118, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 265 82 96 68 161 289), lower := (rows 11 22 164 265 82 96 68 128 256), losses := [] }

theorem u2103 : Upper (D 6) (R 6) [10,20,160,257,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2104 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 265, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 164 265 82 96 96 133 261), lower := (rows 11 22 164 265 82 96 96 128 256), losses := [] }

theorem u2104 : Upper (D 6) (R 6) [10,20,160,257,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2105 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 182, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 265 112 34 65 196 324), lower := (rows 11 22 164 265 112 34 65 128 256), losses := [] }

theorem u2105 : Upper (D 6) (R 6) [10,20,160,257,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2106 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 118, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 265 112 34 68 193 321), lower := (rows 11 22 164 265 112 34 68 128 256), losses := [] }

theorem u2106 : Upper (D 6) (R 6) [10,20,160,257,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2107 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 164 268 81 33 66 224 352), lower := (rows 11 22 164 268 81 33 66 128 256), losses := [] }

theorem u2107 : Upper (D 6) (R 6) [10,20,160,260,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2108 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 80, targets := 6 }], pairs := [(3,0),(4,1),(4,2)], upper := (rows 11 22 164 268 81 33 96 194 322), lower := (rows 11 22 164 268 81 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 100 130 258), good := (rows 394 478 228 332 80 96 96 128 256) }] }

theorem u2108 : Upper (D 6) (R 6) [10,20,160,260,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2109 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 164 268 81 34 65 224 352), lower := (rows 11 22 164 268 81 34 65 128 256), losses := [] }

theorem u2109 : Upper (D 6) (R 6) [10,20,160,260,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2110 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(3,1),(4,2)], upper := (rows 11 22 164 268 81 34 96 193 321), lower := (rows 11 22 164 268 81 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 16 32 100 144 272), good := (rows 9 476 228 332 465 104 96 128 256) },{ target := 5, region := (rows 35 2 4 10 80 0 64 208 336), good := (rows 11 415 133 268 465 11 465 128 256) }] }

theorem u2110 : Upper (D 6) (R 6) [10,20,160,260,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2111 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 164 268 81 96 65 162 290), lower := (rows 11 22 164 268 81 96 65 128 256), losses := [] }

theorem u2111 : Upper (D 6) (R 6) [10,20,160,260,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2112 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 164 268 81 96 66 161 289), lower := (rows 11 22 164 268 81 96 66 128 256), losses := [] }

theorem u2112 : Upper (D 6) (R 6) [10,20,160,260,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2113 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 265, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 164 268 81 96 96 131 259), lower := (rows 11 22 164 268 81 96 96 128 256), losses := [] }

theorem u2113 : Upper (D 6) (R 6) [10,20,160,260,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2114 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 428, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 164 296 81 33 66 196 324), lower := (rows 11 22 164 296 81 33 66 128 256), losses := [] }

theorem u2114 : Upper (D 6) (R 6) [10,20,160,288,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2115 : PairBound 9 := { available := 66, camps := [], pairs := [(2,0),(3,0),(4,1)], upper := (rows 11 22 164 296 81 33 68 194 322), lower := (rows 11 22 164 296 81 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 16 32 110 131 259), good := (rows 458 470 236 364 464 492 68 128 256) },{ target := 1, region := (rows 1 0 4 8 17 49 70 128 256), good := (rows 121 116 228 296 113 49 68 128 256) }] }

theorem u2115 : Upper (D 6) (R 6) [10,20,160,288,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2116 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 22 164 296 81 34 65 196 324), lower := (rows 11 22 164 296 81 34 65 128 256), losses := [] }

theorem u2116 : Upper (D 6) (R 6) [10,20,160,288,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2117 : PairBound 9 := { available := 65, camps := [], pairs := [(0,2),(3,2),(4,1)], upper := (rows 11 22 164 296 81 34 68 193 321), lower := (rows 11 22 164 296 81 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 32 70 145 273), good := (rows 473 468 228 296 465 96 68 128 256) },{ target := 2, region := (rows 35 2 0 26 16 35 64 144 272), good := (rows 43 443 161 297 505 43 64 128 256) }] }

theorem u2117 : Upper (D 6) (R 6) [10,20,160,288,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2118 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 22 164 296 81 96 65 134 262), lower := (rows 11 22 164 296 81 96 65 128 256), losses := [] }

theorem u2118 : Upper (D 6) (R 6) [10,20,160,288,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2119 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 428, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 164 296 81 96 66 133 261), lower := (rows 11 22 164 296 81 96 66 128 256), losses := [] }

theorem u2119 : Upper (D 6) (R 6) [10,20,160,288,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2120 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 11 22 164 296 81 96 68 131 259), lower := (rows 11 22 164 296 81 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 132 8 17 247 198 128 256), good := (rows 121 116 228 296 113 96 100 228 256) }] }

theorem u2120 : Upper (D 6) (R 6) [10,20,160,288,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2121 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 164 296 82 33 65 196 324), lower := (rows 11 22 164 296 82 33 65 128 256), losses := [] }

theorem u2121 : Upper (D 6) (R 6) [10,20,160,288,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2122 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 22 164 296 82 33 68 193 321), lower := (rows 11 22 164 296 82 33 68 128 256), losses := [] }

theorem u2122 : Upper (D 6) (R 6) [10,20,160,288,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2123 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 164 296 82 96 65 133 261), lower := (rows 11 22 164 296 82 96 65 128 256), losses := [] }

theorem u2123 : Upper (D 6) (R 6) [10,20,160,288,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2124 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 118, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 296 82 96 68 129 257), lower := (rows 11 22 164 296 82 96 68 128 256), losses := [] }

theorem u2124 : Upper (D 6) (R 6) [10,20,160,288,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2125 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 328 81 33 66 164 292), lower := (rows 11 22 164 328 81 33 66 128 256), losses := [] }

theorem u2125 : Upper (D 6) (R 6) [10,20,160,320,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2126 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 22 164 328 81 33 68 162 290), lower := (rows 11 22 164 328 81 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 49 70 128 256), good := (rows 121 116 228 328 113 49 68 128 256) }] }

theorem u2126 : Upper (D 6) (R 6) [10,20,160,320,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2127 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(4,1),(4,2)], upper := (rows 11 22 164 328 81 33 96 134 262), lower := (rows 11 22 164 328 81 33 96 128 256), losses := [] }

theorem u2127 : Upper (D 6) (R 6) [10,20,160,320,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2128 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 22 164 328 81 34 65 164 292), lower := (rows 11 22 164 328 81 34 65 128 256), losses := [] }

theorem u2128 : Upper (D 6) (R 6) [10,20,160,320,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2129 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 22 164 328 81 34 68 161 289), lower := (rows 11 22 164 328 81 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 32 70 128 256), good := (rows 89 84 228 328 81 96 68 128 256) }] }

theorem u2129 : Upper (D 6) (R 6) [10,20,160,320,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2130 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 166, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,6),(2,6),(4,2)], upper := (rows 11 22 164 328 81 34 96 133 261), lower := (rows 11 22 164 328 81 34 96 128 256), losses := [] }

theorem u2130 : Upper (D 6) (R 6) [10,20,160,320,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2131 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(0,5),(3,5)], upper := (rows 11 35 22 140 304 96 65 196 324), lower := (rows 11 35 22 140 304 96 65 128 256), losses := [] }

theorem u2131 : Upper (D 6) (R 6) [10,33,18,132,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2132 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 35 22 140 304 96 68 193 321), lower := (rows 11 35 22 140 304 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 19 109 76 129 257), good := (rows 505 433 116 236 304 96 100 128 256) }] }

theorem u2132 : Upper (D 6) (R 6) [10,33,18,132,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2133 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 35 22 140 336 96 65 164 292), lower := (rows 11 35 22 140 336 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 112 64 132 260), good := (rows 10 34 446 396 368 96 96 128 256) }] }

theorem u2133 : Upper (D 6) (R 6) [10,33,18,132,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2134 : PairBound 9 := { available := 33, camps := [], pairs := [(0,6),(3,1),(4,1)], upper := (rows 11 35 22 140 336 96 68 161 289), lower := (rows 11 35 22 140 336 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 21 125 76 131 259), good := (rows 505 433 508 252 368 96 124 128 256) },{ target := 6, region := (rows 5 2 4 12 16 32 0 130 258), good := (rows 395 419 415 141 272 32 13 128 256) }] }

theorem u2134 : Upper (D 6) (R 6) [10,33,18,132,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2135 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 22 140 336 96 96 133 261), lower := (rows 11 35 22 140 336 96 96 128 256), losses := [] }

theorem u2135 : Upper (D 6) (R 6) [10,33,18,132,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2136 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 35 22 200 84 288 65 164 292), lower := (rows 11 35 22 200 84 288 65 128 256), losses := [] }

theorem u2136 : Upper (D 6) (R 6) [10,33,18,192,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2136 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2137 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 84, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 11 35 22 200 84 288 68 161 289), lower := (rows 11 35 22 200 84 288 68 128 256), losses := [] }

theorem u2137 : Upper (D 6) (R 6) [10,33,18,192,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2137 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2138 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 22 200 84 288 96 133 261), lower := (rows 11 35 22 200 84 288 96 128 256), losses := [] }

theorem u2138 : Upper (D 6) (R 6) [10,33,18,192,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2138 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2139 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 457, targets := 32 },{ cop := 1, region := 80, targets := 2 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 35 22 200 112 36 65 388 260), lower := (rows 11 35 22 200 112 36 65 128 256), losses := [] }

theorem u2139 : Upper (D 6) (R 6) [10,33,18,192,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2140 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 395, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 22 200 112 36 68 385 257), lower := (rows 11 35 22 200 112 36 68 128 256), losses := [] }

theorem u2140 : Upper (D 6) (R 6) [10,33,18,192,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2141 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 22 200 112 36 320 133 261), lower := (rows 11 35 22 200 112 36 320 128 256), losses := [] }

theorem u2141 : Upper (D 6) (R 6) [10,33,18,192,96,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2141 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2142 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 35 22 200 304 36 65 196 324), lower := (rows 11 35 22 200 304 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 5 72 88 103 64 192 320), good := (rows 62 38 54 504 304 36 508 128 256) }] }

theorem u2142 : Upper (D 6) (R 6) [10,33,18,192,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2143 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(3,1),(3,5)], upper := (rows 11 35 22 200 304 36 68 193 321), lower := (rows 11 35 22 200 304 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 14 22 100 100 130 258), good := (rows 409 505 508 232 368 124 124 128 256) }] }

theorem u2143 : Upper (D 6) (R 6) [10,33,18,192,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2144 : PairBound 9 := { available := 36, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 22 200 336 36 65 164 292), lower := (rows 11 35 22 200 336 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 5 88 88 103 64 231 359), good := (rows 446 422 446 504 504 420 508 128 256) }] }

theorem u2144 : Upper (D 6) (R 6) [10,33,18,192,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2145 : PairBound 9 := { available := 33, camps := [], pairs := [(0,6),(3,1),(4,1)], upper := (rows 11 35 22 200 336 36 68 161 289), lower := (rows 11 35 22 200 336 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 14 22 100 100 130 258), good := (rows 409 505 508 232 368 124 124 128 256) },{ target := 6, region := (rows 9 10 4 8 16 100 0 138 266), good := (rows 395 419 438 427 304 36 36 128 256) }] }

theorem u2145 : Upper (D 6) (R 6) [10,33,18,192,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2146 : Route 9 := (fun mask => (mask,id))

def c2146 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2146 : Upper (D 6) (R 6) [10,33,18,192,320,4,32] 13 := by
  apply FastRouting.sound _ _ [10,33,18,192,320,4,32] 13 (by decide) (choices 1) [1,4] r2146 c2146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u114
  · exact u115

def b2147 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 35 22 392 84 96 65 164 292), lower := (rows 11 35 22 392 84 96 65 128 256), losses := [] }

theorem u2147 : Upper (D 6) (R 6) [10,33,18,384,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2148 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 392 84 96 68 161 289), lower := (rows 11 35 22 392 84 96 68 128 256), losses := [] }

theorem u2148 : Upper (D 6) (R 6) [10,33,18,384,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2149 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 393, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 22 392 84 96 96 133 261), lower := (rows 11 35 22 392 84 96 96 128 256), losses := [] }

theorem u2149 : Upper (D 6) (R 6) [10,33,18,384,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2150 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 457, targets := 32 },{ cop := 1, region := 80, targets := 2 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 35 22 392 112 36 65 196 324), lower := (rows 11 35 22 392 112 36 65 128 256), losses := [] }

theorem u2150 : Upper (D 6) (R 6) [10,33,18,384,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2151 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 395, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 22 392 112 36 68 193 321), lower := (rows 11 35 22 392 112 36 68 128 256), losses := [] }

theorem u2151 : Upper (D 6) (R 6) [10,33,18,384,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2152 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0)], upper := (rows 11 35 52 76 145 288 66 196 324), lower := (rows 11 35 52 76 145 288 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 317 67 152 280), good := (rows 490 98 444 492 508 288 66 128 288) }] }

theorem u2152 : Upper (D 6) (R 6) [10,33,48,68,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2152 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2153 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 52 76 145 288 68 194 322), lower := (rows 11 35 52 76 145 288 68 128 256), losses := [] }

theorem u2153 : Upper (D 6) (R 6) [10,33,48,68,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2153 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2154 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0)], upper := (rows 11 35 52 76 146 288 65 196 324), lower := (rows 11 35 52 76 146 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 71 72 17 361 64 200 328), good := (rows 446 54 52 492 150 288 508 128 288) }] }

theorem u2154 : Upper (D 6) (R 6) [10,33,48,68,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2154 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2155 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 52 76 146 288 68 193 321), lower := (rows 11 35 52 76 146 288 68 128 256), losses := [] }

theorem u2155 : Upper (D 6) (R 6) [10,33,48,68,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2155 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2156 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 52 137 276 96 66 196 324), lower := (rows 11 35 52 137 276 96 66 128 256), losses := [] }

theorem u2156 : Upper (D 6) (R 6) [10,33,48,129,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2157 : PairBound 9 := { available := 66, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 52 137 276 96 68 194 322), lower := (rows 11 35 52 137 276 96 68 128 256), losses := [] }

theorem u2157 : Upper (D 6) (R 6) [10,33,48,129,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2158 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 52 140 81 288 66 196 324), lower := (rows 11 35 52 140 81 288 66 128 256), losses := [] }

theorem u2158 : Upper (D 6) (R 6) [10,33,48,132,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2158 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2159 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 35 52 140 81 288 68 194 322), lower := (rows 11 35 52 140 81 288 68 128 256), losses := [] }

theorem u2159 : Upper (D 6) (R 6) [10,33,48,132,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2159 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2159
end Delivery.IrregularNine14.P06
