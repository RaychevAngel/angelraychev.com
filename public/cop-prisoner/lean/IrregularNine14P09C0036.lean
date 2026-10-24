import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0002

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2160 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 4, region := 297, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 7 134 56 208 288 320 137 265), lower := (rows 97 7 134 56 208 288 320 128 256), losses := [] }

theorem u2160 : Upper (D 9) (R 9) [96,5,130,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2160 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2161 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 5, region := 345, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,5)], upper := (rows 97 7 134 56 273 160 72 448 320), lower := (rows 97 7 134 56 273 160 72 128 256), losses := [] }

theorem u2161 : Upper (D 9) (R 9) [96,5,130,48,257,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2161 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2162 : Route 9 := (fun mask => (mask,id))

def c2162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2162 : Upper (D 9) (R 9) [96,5,130,48,257,128,256] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,257,128,256] 13 (by decide) (choices 1) [8,64] r2162 c2162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u122
  · exact u123

def b2163 : PairBound 9 := { available := 264, camps := [{ cop := 5, region := 345, targets := 128 },{ cop := 5, region := 71, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 134 56 336 160 65 392 264), lower := (rows 97 7 134 56 336 160 65 128 256), losses := [] }

theorem u2163 : Upper (D 9) (R 9) [96,5,130,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2163 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2164 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 5, region := 345, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,5)], upper := (rows 97 7 134 56 336 160 72 385 257), lower := (rows 97 7 134 56 336 160 72 128 256), losses := [] }

theorem u2164 : Upper (D 9) (R 9) [96,5,130,48,320,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2164 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2165 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 5, region := 345, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 134 56 336 160 320 137 265), lower := (rows 97 7 134 56 336 160 320 128 256), losses := [] }

theorem u2165 : Upper (D 9) (R 9) [96,5,130,48,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2165 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2166 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(4,7)], upper := (rows 97 7 134 152 273 40 320 224 352), lower := (rows 97 7 134 152 273 40 320 128 256), losses := [] }

theorem u2166 : Upper (D 9) (R 9) [96,5,130,144,257,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2166 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2167 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 152 273 96 320 168 296), lower := (rows 97 7 134 152 273 96 320 128 256), losses := [] }

theorem u2167 : Upper (D 9) (R 9) [96,5,130,144,257,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2167 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2168 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 3, region := 65, targets := 256 }], pairs := [(0,8),(1,5),(2,5),(4,5)], upper := (rows 97 7 134 168 273 288 72 208 336), lower := (rows 97 7 134 168 273 288 72 128 256), losses := [] }

theorem u2168 : Upper (D 9) (R 9) [96,5,130,160,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2168 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2169 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 7 134 168 273 288 80 200 328), lower := (rows 97 7 134 168 273 288 80 128 256), losses := [] }

theorem u2169 : Upper (D 9) (R 9) [96,5,130,160,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2169 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2170 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 0, region := 408, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,0)], upper := (rows 97 7 134 168 280 288 65 208 336), lower := (rows 97 7 134 168 280 288 65 128 256), losses := [] }

theorem u2170 : Upper (D 9) (R 9) [96,5,130,160,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2170 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2171 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 134, targets := 32 }], pairs := [(1,5),(1,8),(2,8),(3,8)], upper := (rows 97 7 134 168 280 288 80 193 321), lower := (rows 97 7 134 168 280 288 80 128 256), losses := [] }

theorem u2171 : Upper (D 9) (R 9) [96,5,130,160,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2171 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2172 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 0, region := 408, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,0)], upper := (rows 97 7 134 168 336 288 65 152 280), lower := (rows 97 7 134 168 336 288 65 128 256), losses := [] }

theorem u2172 : Upper (D 9) (R 9) [96,5,130,160,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2172 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2173 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 3, region := 65, targets := 256 }], pairs := [(0,8),(1,5),(2,5),(4,5)], upper := (rows 97 7 134 168 336 288 72 145 273), lower := (rows 97 7 134 168 336 288 72 128 256), losses := [] }

theorem u2173 : Upper (D 9) (R 9) [96,5,130,160,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2173 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2174 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 64 },{ cop := 0, region := 142, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(3,6)], upper := (rows 97 7 134 168 336 288 80 137 265), lower := (rows 97 7 134 168 336 288 80 128 256), losses := [] }

theorem u2174 : Upper (D 9) (R 9) [96,5,130,160,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2174 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2175 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 345, targets := 128 },{ cop := 0, region := 272, targets := 1 }], pairs := [(0,7),(3,7),(4,0),(4,7)], upper := (rows 97 7 134 265 304 160 72 208 336), lower := (rows 97 7 134 265 304 160 72 128 256), losses := [] }

theorem u2175 : Upper (D 9) (R 9) [96,5,130,257,288,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2175 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2176 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 5, region := 345, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5)], upper := (rows 97 7 134 265 304 160 80 200 328), lower := (rows 97 7 134 265 304 160 80 128 256), losses := [] }

theorem u2176 : Upper (D 9) (R 9) [96,5,130,257,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2176 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2177 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(1,8),(2,8)], upper := (rows 97 7 134 265 400 40 80 224 352), lower := (rows 97 7 134 265 400 40 80 128 256), losses := [] }

theorem u2177 : Upper (D 9) (R 9) [96,5,130,257,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2177 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2178 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 134 265 400 48 96 200 328), lower := (rows 97 7 134 265 400 48 96 128 256), losses := [] }

theorem u2178 : Upper (D 9) (R 9) [96,5,130,257,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2178 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2179 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 313, targets := 128 },{ cop := 6, region := 39, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 134 296 336 33 192 152 280), lower := (rows 97 7 134 296 336 33 192 128 256), losses := [] }

theorem u2179 : Upper (D 9) (R 9) [96,5,130,288,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2179 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2180 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 6, region := 313, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,5)], upper := (rows 97 7 134 296 336 40 192 145 273), lower := (rows 97 7 134 296 336 40 192 128 256), losses := [] }

theorem u2180 : Upper (D 9) (R 9) [96,5,130,288,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2180 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2181 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 193, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6)], upper := (rows 97 7 134 296 336 48 192 137 265), lower := (rows 97 7 134 296 336 48 192 128 256), losses := [] }

theorem u2181 : Upper (D 9) (R 9) [96,5,130,288,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2181 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2182 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 140 25 304 160 66 448 320), lower := (rows 97 7 140 25 304 160 66 128 256), losses := [] }

theorem u2182 : Upper (D 9) (R 9) [96,5,136,17,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2182 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2183 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 4, region := 73, targets := 128 },{ cop := 1, region := 496, targets := 1 }], pairs := [(0,7),(1,5),(2,5),(3,7),(4,0)], upper := (rows 97 7 140 25 304 160 320 194 322), lower := (rows 97 7 140 25 304 160 320 128 256), losses := [] }

theorem u2183 : Upper (D 9) (R 9) [96,5,136,17,288,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2183 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2184 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 97 7 140 25 400 34 320 224 352), lower := (rows 97 7 140 25 400 34 320 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 59 34 379 163 291), good := (rows 496 502 220 476 464 498 320 128 320) }] }

theorem u2184 : Upper (D 9) (R 9) [96,5,136,17,384,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2184 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2185 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 25 400 96 320 162 290), lower := (rows 97 7 140 25 400 96 320 128 256), losses := [] }

theorem u2185 : Upper (D 9) (R 9) [96,5,136,17,384,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2185 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2186 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 140 26 176 288 65 448 320), lower := (rows 97 7 140 26 176 288 65 128 256), losses := [] }

theorem u2186 : Upper (D 9) (R 9) [96,5,136,18,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2186 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2187 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 7 140 26 176 288 320 193 321), lower := (rows 97 7 140 26 176 288 320 128 256), losses := [] }

theorem u2187 : Upper (D 9) (R 9) [96,5,136,18,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2187 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2188 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 97, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 26 273 96 192 416 288), lower := (rows 97 7 140 26 273 96 192 128 256), losses := [] }

theorem u2188 : Upper (D 9) (R 9) [96,5,136,18,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2188 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2189 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 337, targets := 128 },{ cop := 3, region := 484, targets := 1 },{ cop := 6, region := 161, targets := 256 }], pairs := [(0,7),(0,8),(2,0),(3,7),(4,7)], upper := (rows 97 7 140 26 273 160 320 224 352), lower := (rows 97 7 140 26 273 160 320 128 256), losses := [{ target := 7, region := (rows 33 2 4 10 51 32 371 0 289), good := (rows 369 351 12 90 337 369 320 0 320) }] }

theorem u2189 : Upper (D 9) (R 9) [96,5,136,18,257,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2189 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2190 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 99, targets := 256 },{ cop := 5, region := 337, targets := 128 },{ cop := 0, region := 272, targets := 1 }], pairs := [(0,7),(0,8),(1,8),(4,0),(4,7)], upper := (rows 97 7 140 26 304 160 65 448 320), lower := (rows 97 7 140 26 304 160 65 128 256), losses := [] }

theorem u2190 : Upper (D 9) (R 9) [96,5,136,18,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2190 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2191 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 337, targets := 128 },{ cop := 6, region := 161, targets := 256 }], pairs := [(0,7),(0,8),(2,5),(3,7),(4,7)], upper := (rows 97 7 140 26 304 160 320 193 321), lower := (rows 97 7 140 26 304 160 320 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 347 131 259), good := (rows 449 455 204 478 336 128 320 128 320) },{ target := 7, region := (rows 49 2 4 10 49 32 383 0 315), good := (rows 369 351 332 347 369 369 320 0 320) }] }

theorem u2191 : Upper (D 9) (R 9) [96,5,136,18,288,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2191 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2192 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 1 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(2,0),(4,0)], upper := (rows 97 7 140 26 400 33 320 224 352), lower := (rows 97 7 140 26 400 33 320 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 51 32 371 161 289), good := (rows 496 478 140 94 464 496 320 128 320) }] }

theorem u2192 : Upper (D 9) (R 9) [96,5,136,18,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2192 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2193 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 26 400 96 320 161 289), lower := (rows 97 7 140 26 400 96 320 128 256), losses := [] }

theorem u2193 : Upper (D 9) (R 9) [96,5,136,18,384,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2193 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2194 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 400, targets := 32 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,5)], upper := (rows 97 7 140 42 145 288 80 448 320), lower := (rows 97 7 140 42 145 288 80 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 16 371 80 209 337), good := (rows 480 430 140 46 496 288 496 128 288) }] }

theorem u2194 : Upper (D 9) (R 9) [96,5,136,34,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2194 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2195 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5),(4,8)], upper := (rows 97 7 140 42 145 288 320 208 336), lower := (rows 97 7 140 42 145 288 320 128 256), losses := [] }

theorem u2195 : Upper (D 9) (R 9) [96,5,136,34,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2195 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2196 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 1 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(2,0),(4,0),(4,5)], upper := (rows 97 7 140 42 208 288 65 400 272), lower := (rows 97 7 140 42 208 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 14 10 81 379 64 211 339), good := (rows 496 446 172 430 496 288 496 128 288) }] }

theorem u2196 : Upper (D 9) (R 9) [96,5,136,34,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2196 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2197 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 2, region := 80, targets := 1 }], pairs := [(1,6),(2,6),(3,6),(4,0)], upper := (rows 97 7 140 42 208 288 80 385 257), lower := (rows 97 7 140 42 208 288 80 128 256), losses := [] }

theorem u2197 : Upper (D 9) (R 9) [96,5,136,34,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2197 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2198 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5),(4,8)], upper := (rows 97 7 140 42 208 288 320 145 273), lower := (rows 97 7 140 42 208 288 320 128 256), losses := [] }

theorem u2198 : Upper (D 9) (R 9) [96,5,136,34,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2198 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2199 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 452, targets := 33 },{ cop := 6, region := 305, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(4,7)], upper := (rows 97 7 140 42 273 48 192 448 320), lower := (rows 97 7 140 42 273 48 192 128 256), losses := [] }

theorem u2199 : Upper (D 9) (R 9) [96,5,136,34,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2199 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2200 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 3, region := 452, targets := 1 }], pairs := [(1,8),(2,0),(2,8),(3,8)], upper := (rows 97 7 140 42 273 48 320 192 448), lower := (rows 97 7 140 42 273 48 320 128 256), losses := [] }

theorem u2200 : Upper (D 9) (R 9) [96,5,136,34,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2200 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2201 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 5, region := 81, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 7 140 42 273 288 80 192 448), lower := (rows 97 7 140 42 273 288 80 128 256), losses := [] }

theorem u2201 : Upper (D 9) (R 9) [96,5,136,34,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2201 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2202 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 305, targets := 128 },{ cop := 0, region := 272, targets := 32 }], pairs := [(0,7),(2,5),(3,7),(4,5),(4,7)], upper := (rows 97 7 140 42 273 288 192 208 336), lower := (rows 97 7 140 42 273 288 192 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 19 0 223 155 283), good := (rows 465 471 460 478 465 256 192 192 256) },{ target := 7, region := (rows 65 2 4 10 83 371 64 0 321), good := (rows 369 319 12 58 305 288 369 0 288) }] }

theorem u2202 : Upper (D 9) (R 9) [96,5,136,34,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2202 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2203 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 1 },{ cop := 0, region := 400, targets := 32 },{ cop := 5, region := 81, targets := 128 }], pairs := [(0,7),(0,8),(4,0),(4,5),(4,7)], upper := (rows 97 7 140 42 336 288 65 144 400), lower := (rows 97 7 140 42 336 288 65 128 256), losses := [] }

theorem u2203 : Upper (D 9) (R 9) [96,5,136,34,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2203 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2204 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 142, targets := 64 },{ cop := 0, region := 142, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(3,6)], upper := (rows 97 7 140 42 336 288 80 129 385), lower := (rows 97 7 140 42 336 288 80 128 256), losses := [] }

theorem u2204 : Upper (D 9) (R 9) [96,5,136,34,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2204 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2205 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 305, targets := 128 },{ cop := 0, region := 272, targets := 32 }], pairs := [(0,7),(2,5),(3,7),(4,5),(4,7)], upper := (rows 97 7 140 42 336 288 192 145 273), lower := (rows 97 7 140 42 336 288 192 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 27 0 207 131 259), good := (rows 465 471 220 478 336 256 192 192 256) },{ target := 7, region := (rows 81 2 4 10 81 379 64 0 339), good := (rows 369 319 44 298 369 288 369 0 288) }] }

theorem u2205 : Upper (D 9) (R 9) [96,5,136,34,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2205 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2206 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 1 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(2,0),(4,0),(4,5)], upper := (rows 97 7 140 42 400 288 65 208 336), lower := (rows 97 7 140 42 400 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 83 371 64 193 321), good := (rows 496 446 140 62 432 288 496 128 288) }] }

theorem u2206 : Upper (D 9) (R 9) [96,5,136,34,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2206 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2207 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 400, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5)], upper := (rows 97 7 140 42 400 288 80 193 321), lower := (rows 97 7 140 42 400 288 80 128 256), losses := [] }

theorem u2207 : Upper (D 9) (R 9) [96,5,136,34,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2207 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2208 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 428, targets := 65 },{ cop := 1, region := 80, targets := 128 }], pairs := [(2,0),(2,6),(3,0),(3,6),(4,7)], upper := (rows 97 7 140 56 82 288 65 384 384), lower := (rows 97 7 140 56 82 288 65 128 256), losses := [] }

theorem u2208 : Upper (D 9) (R 9) [96,5,136,48,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2208 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2209 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 297, targets := 128 },{ cop := 1, region := 464, targets := 32 }], pairs := [(0,7),(2,6),(3,7),(4,0),(4,5)], upper := (rows 97 7 140 56 82 288 192 385 257), lower := (rows 97 7 140 56 82 288 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 288 196 128 256), good := (rows 96 86 204 56 82 288 192 192 288) },{ target := 6, region := (rows 1 2 20 24 16 307 0 131 259), good := (rows 417 423 140 60 446 288 128 128 288) }] }

theorem u2209 : Upper (D 9) (R 9) [96,5,136,48,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2209 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2210 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 464, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5),(4,8)], upper := (rows 97 7 140 56 82 288 320 129 385), lower := (rows 97 7 140 56 82 288 320 128 256), losses := [] }

theorem u2210 : Upper (D 9) (R 9) [96,5,136,48,66,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2210 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2211 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(1,7),(2,0),(4,5)], upper := (rows 97 7 140 56 145 288 66 448 320), lower := (rows 97 7 140 56 145 288 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 371 66 195 323), good := (rows 480 486 140 60 444 288 482 128 288) }] }

theorem u2211 : Upper (D 9) (R 9) [96,5,136,48,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2211 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2212 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 7 140 56 145 288 320 194 322), lower := (rows 97 7 140 56 145 288 320 128 256), losses := [] }

theorem u2212 : Upper (D 9) (R 9) [96,5,136,48,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2212 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2213 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 464, targets := 32 },{ cop := 3, region := 65, targets := 256 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(3,7),(4,5)], upper := (rows 97 7 140 56 146 288 65 448 320), lower := (rows 97 7 140 56 146 288 65 128 256), losses := [] }

theorem u2213 : Upper (D 9) (R 9) [96,5,136,48,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2213 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2214 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 7 140 56 146 288 320 193 321), lower := (rows 97 7 140 56 146 288 320 128 256), losses := [] }

theorem u2214 : Upper (D 9) (R 9) [96,5,136,48,130,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2214 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2215 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 464, targets := 32 },{ cop := 3, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,5)], upper := (rows 97 7 140 56 208 288 65 386 258), lower := (rows 97 7 140 56 208 288 65 128 256), losses := [{ target := 8, region := (rows 41 6 4 8 20 32 111 128 0), good := (rows 97 87 223 121 208 97 65 128 0) }] }

theorem u2215 : Upper (D 9) (R 9) [96,5,136,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2215 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2216 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 32 },{ cop := 4, region := 297, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,5)], upper := (rows 97 7 140 56 208 288 66 385 257), lower := (rows 97 7 140 56 208 288 66 128 256), losses := [] }

theorem u2216 : Upper (D 9) (R 9) [96,5,136,48,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2216 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2217 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 7 140 56 208 288 320 131 259), lower := (rows 97 7 140 56 208 288 320 128 256), losses := [] }

theorem u2217 : Upper (D 9) (R 9) [96,5,136,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2217 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2218 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 140 56 273 34 192 448 320), lower := (rows 97 7 140 56 273 34 192 128 256), losses := [] }

theorem u2218 : Upper (D 9) (R 9) [96,5,136,48,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2218 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2219 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 452, targets := 33 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(2,0),(2,5),(4,5)], upper := (rows 97 7 140 56 273 34 320 192 448), lower := (rows 97 7 140 56 273 34 320 128 256), losses := [{ target := 7, region := (rows 9 6 4 8 16 38 336 0 256), good := (rows 97 39 47 121 337 34 320 0 320) }] }

theorem u2219 : Upper (D 9) (R 9) [96,5,136,48,257,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2219 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2219
end Delivery.IrregularNine14.P09
