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

def b2040 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 5, region := 81, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 7 14 168 273 288 80 192 448), lower := (rows 97 7 14 168 273 288 80 128 256), losses := [] }

theorem u2040 : Upper (D 9) (R 9) [96,5,10,160,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2040 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2041 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 6, region := 305, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,7)], upper := (rows 97 7 14 168 273 288 192 208 336), lower := (rows 97 7 14 168 273 288 192 128 256), losses := [] }

theorem u2041 : Upper (D 9) (R 9) [96,5,10,160,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2041 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2042 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 7 14 168 336 288 65 144 400), lower := (rows 97 7 14 168 336 288 65 128 256), losses := [] }

theorem u2042 : Upper (D 9) (R 9) [96,5,10,160,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2042 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2043 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 142, targets := 64 },{ cop := 0, region := 142, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(3,6)], upper := (rows 97 7 14 168 336 288 80 129 385), lower := (rows 97 7 14 168 336 288 80 128 256), losses := [] }

theorem u2043 : Upper (D 9) (R 9) [96,5,10,160,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2043 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2044 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 6, region := 305, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,7)], upper := (rows 97 7 14 168 336 288 192 145 273), lower := (rows 97 7 14 168 336 288 192 128 256), losses := [] }

theorem u2044 : Upper (D 9) (R 9) [96,5,10,160,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2044 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2045 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 7 14 168 400 288 65 208 336), lower := (rows 97 7 14 168 400 288 65 128 256), losses := [] }

theorem u2045 : Upper (D 9) (R 9) [96,5,10,160,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2045 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2046 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 400, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5)], upper := (rows 97 7 14 168 400 288 80 193 321), lower := (rows 97 7 14 168 400 288 80 128 256), losses := [] }

theorem u2046 : Upper (D 9) (R 9) [96,5,10,160,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2046 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2047 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 14 392 145 48 96 448 320), lower := (rows 97 7 14 392 145 48 96 128 256), losses := [] }

theorem u2047 : Upper (D 9) (R 9) [96,5,10,384,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2047 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2048 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 177, targets := 256 },{ cop := 0, region := 392, targets := 1 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(3,0),(4,8)], upper := (rows 97 7 14 392 145 48 320 224 352), lower := (rows 97 7 14 392 145 48 320 128 256), losses := [] }

theorem u2048 : Upper (D 9) (R 9) [96,5,10,384,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2048 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2049 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 14 392 145 96 320 176 304), lower := (rows 97 7 14 392 145 96 320 128 256), losses := [] }

theorem u2049 : Upper (D 9) (R 9) [96,5,10,384,129,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2049 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2050 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 400, targets := 32 },{ cop := 1, region := 488, targets := 1 },{ cop := 6, region := 289, targets := 128 }], pairs := [(0,7),(1,7),(2,5),(3,0),(4,5)], upper := (rows 97 7 28 42 145 288 192 448 320), lower := (rows 97 7 28 42 145 288 192 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 19 0 511 511 511), good := (rows 465 471 476 478 465 448 448 448 448) },{ target := 7, region := (rows 65 18 20 30 16 371 64 0 321), good := (rows 353 303 62 42 319 288 353 0 288) }] }

theorem u2050 : Upper (D 9) (R 9) [96,5,24,34,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2050 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2051 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5),(4,8)], upper := (rows 97 7 28 42 145 288 320 192 448), lower := (rows 97 7 28 42 145 288 320 128 256), losses := [] }

theorem u2051 : Upper (D 9) (R 9) [96,5,24,34,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2051 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2052 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 424, targets := 65 },{ cop := 3, region := 65, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,6),(4,0)], upper := (rows 97 7 28 42 208 288 65 384 384), lower := (rows 97 7 28 42 208 288 65 128 256), losses := [] }

theorem u2052 : Upper (D 9) (R 9) [96,5,24,34,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2052 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2053 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 97 7 28 42 208 288 192 385 257), lower := (rows 97 7 28 42 208 288 192 128 256), losses := [] }

theorem u2053 : Upper (D 9) (R 9) [96,5,24,34,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2053 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2054 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,8),(2,8),(3,8),(4,5),(4,8)], upper := (rows 97 7 28 42 208 288 320 129 385), lower := (rows 97 7 28 42 208 288 320 128 256), losses := [] }

theorem u2054 : Upper (D 9) (R 9) [96,5,24,34,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2054 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2055 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 28 42 400 160 65 448 320), lower := (rows 97 7 28 42 400 160 65 128 256), losses := [] }

theorem u2055 : Upper (D 9) (R 9) [96,5,24,34,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2055 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2056 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 400, targets := 32 },{ cop := 3, region := 321, targets := 128 },{ cop := 6, region := 161, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(2,5),(4,5)], upper := (rows 97 7 28 42 400 160 320 193 321), lower := (rows 97 7 28 42 400 160 320 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 27 0 347 131 259), good := (rows 465 471 92 478 464 128 320 128 320) },{ target := 7, region := (rows 41 6 4 8 16 32 383 0 303), good := (rows 353 327 351 363 336 353 320 0 320) }] }

theorem u2056 : Upper (D 9) (R 9) [96,5,24,34,384,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2056 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2057 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 28 137 176 288 66 448 320), lower := (rows 97 7 28 137 176 288 66 128 256), losses := [] }

theorem u2057 : Upper (D 9) (R 9) [96,5,24,129,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2057 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2058 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 7 28 137 176 288 320 194 322), lower := (rows 97 7 28 137 176 288 320 128 256), losses := [] }

theorem u2058 : Upper (D 9) (R 9) [96,5,24,129,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2058 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2059 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 137 274 96 320 160 416), lower := (rows 97 7 28 137 274 96 320 128 256), losses := [] }

theorem u2059 : Upper (D 9) (R 9) [96,5,24,129,258,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2059 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2060 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 169, targets := 256 },{ cop := 1, region := 496, targets := 1 },{ cop := 5, region := 321, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(3,8),(4,0)], upper := (rows 97 7 28 137 274 160 320 224 352), lower := (rows 97 7 28 137 274 160 320 128 256), losses := [{ target := 7, region := (rows 33 10 12 8 26 32 379 0 289), good := (rows 353 343 94 351 338 353 320 0 320) }] }

theorem u2060 : Upper (D 9) (R 9) [96,5,24,129,258,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2060 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2061 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 272, targets := 1 },{ cop := 0, region := 392, targets := 32 },{ cop := 0, region := 272, targets := 128 }], pairs := [(2,0),(3,5),(4,0),(4,7)], upper := (rows 97 7 28 137 304 34 192 448 320), lower := (rows 97 7 28 137 304 34 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 51 34 511 511 511), good := (rows 496 502 476 476 496 498 448 448 448) }] }

theorem u2061 : Upper (D 9) (R 9) [96,5,24,129,288,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2061 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2062 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 400, targets := 1 },{ cop := 0, region := 136, targets := 32 },{ cop := 0, region := 136, targets := 256 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7),(3,5),(3,8),(4,0)], upper := (rows 97 7 28 137 304 34 320 192 448), lower := (rows 97 7 28 137 304 34 320 128 256), losses := [] }

theorem u2062 : Upper (D 9) (R 9) [96,5,24,129,288,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2062 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2063 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 272, targets := 1 },{ cop := 0, region := 392, targets := 32 },{ cop := 0, region := 272, targets := 128 }], pairs := [(2,0),(3,5),(4,0),(4,7)], upper := (rows 97 7 28 137 304 160 66 448 320), lower := (rows 97 7 28 137 304 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 91 235 66 195 323), good := (rows 496 502 60 444 304 160 498 160 256) }] }

theorem u2063 : Upper (D 9) (R 9) [96,5,24,129,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2063 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2064 : Route 9 := (fun mask => (mask,id))

def c2064 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2064 : Upper (D 9) (R 9) [96,5,24,129,288,128,256] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,288,128,256] 13 (by decide) (choices 1) [2,64] r2064 c2064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u120
  · exact u121

def b2065 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 1 },{ cop := 0, region := 136, targets := 256 }], pairs := [(0,7),(1,7),(3,8),(4,0)], upper := (rows 97 7 28 137 400 34 320 224 352), lower := (rows 97 7 28 137 400 34 320 128 256), losses := [] }

theorem u2065 : Upper (D 9) (R 9) [96,5,24,129,384,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2065 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2066 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 137 400 96 320 162 290), lower := (rows 97 7 28 137 400 96 320 128 256), losses := [] }

theorem u2066 : Upper (D 9) (R 9) [96,5,24,129,384,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2066 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2067 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 28 138 176 288 65 448 320), lower := (rows 97 7 28 138 176 288 65 128 256), losses := [] }

theorem u2067 : Upper (D 9) (R 9) [96,5,24,130,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2067 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2068 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 7 28 138 176 288 320 193 321), lower := (rows 97 7 28 138 176 288 320 128 256), losses := [] }

theorem u2068 : Upper (D 9) (R 9) [96,5,24,130,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2068 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2069 : PairBound 9 := { available := 320, camps := [{ cop := 5, region := 337, targets := 128 },{ cop := 0, region := 272, targets := 1 },{ cop := 1, region := 456, targets := 32 },{ cop := 3, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(3,5),(4,0),(4,7)], upper := (rows 97 7 28 138 304 160 65 448 320), lower := (rows 97 7 28 138 304 160 65 128 256), losses := [] }

theorem u2069 : Upper (D 9) (R 9) [96,5,24,130,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2069 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2070 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 337, targets := 128 },{ cop := 1, region := 456, targets := 32 },{ cop := 6, region := 161, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(3,5),(4,7)], upper := (rows 97 7 28 138 304 160 320 193 321), lower := (rows 97 7 28 138 304 160 320 128 256), losses := [{ target := 7, region := (rows 49 6 4 8 49 32 383 0 311), good := (rows 369 343 351 330 369 369 320 0 320) }] }

theorem u2070 : Upper (D 9) (R 9) [96,5,24,130,288,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2070 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2071 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 1 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(2,0),(4,0)], upper := (rows 97 7 28 138 400 33 320 224 352), lower := (rows 97 7 28 138 400 33 320 128 256), losses := [{ target := 0, region := (rows 0 2 14 10 51 32 371 161 289), good := (rows 496 478 92 222 464 496 320 128 320) }] }

theorem u2071 : Upper (D 9) (R 9) [96,5,24,130,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2071 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2072 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 138 400 96 320 161 289), lower := (rows 97 7 28 138 400 96 320 128 256), losses := [] }

theorem u2072 : Upper (D 9) (R 9) [96,5,24,130,384,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2072 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2073 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 1, region := 464, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 28 168 208 33 320 386 258), lower := (rows 97 7 28 168 208 33 320 128 256), losses := [] }

theorem u2073 : Upper (D 9) (R 9) [96,5,24,160,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2073 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2074 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 28 168 208 34 320 385 257), lower := (rows 97 7 28 168 208 34 320 128 256), losses := [] }

theorem u2074 : Upper (D 9) (R 9) [96,5,24,160,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2074 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2075 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 7 28 168 208 288 320 131 259), lower := (rows 97 7 28 168 208 288 320 128 256), losses := [] }

theorem u2075 : Upper (D 9) (R 9) [96,5,24,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2075 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2076 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 28 168 336 33 66 384 384), lower := (rows 97 7 28 168 336 33 66 128 256), losses := [] }

theorem u2076 : Upper (D 9) (R 9) [96,5,24,160,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2076 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2077 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 33, targets := 384 },{ cop := 1, region := 424, targets := 64 }], pairs := [(0,7),(0,8),(3,6),(4,0),(4,5)], upper := (rows 97 7 28 168 336 33 192 386 258), lower := (rows 97 7 28 168 336 33 192 128 256), losses := [] }

theorem u2077 : Upper (D 9) (R 9) [96,5,24,160,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2077 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2078 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 272, targets := 32 },{ cop := 0, region := 392, targets := 64 },{ cop := 0, region := 272, targets := 128 },{ cop := 3, region := 65, targets := 256 }], pairs := [(0,8),(3,6),(4,5),(4,7)], upper := (rows 97 7 28 168 336 34 192 385 257), lower := (rows 97 7 28 168 336 34 192 128 256), losses := [] }

theorem u2078 : Upper (D 9) (R 9) [96,5,24,160,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2078 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2079 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 28 168 336 34 320 129 385), lower := (rows 97 7 28 168 336 34 320 128 256), losses := [] }

theorem u2079 : Upper (D 9) (R 9) [96,5,24,160,320,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2079 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2080 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 464, targets := 32 },{ cop := 1, region := 424, targets := 64 },{ cop := 3, region := 65, targets := 256 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(3,6),(4,5)], upper := (rows 97 7 28 168 336 288 192 131 259), lower := (rows 97 7 28 168 336 288 192 128 256), losses := [{ target := 7, region := (rows 17 6 4 8 16 310 64 0 262), good := (rows 97 295 319 40 369 288 64 0 288) }] }

theorem u2080 : Upper (D 9) (R 9) [96,5,24,160,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2080 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2081 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 464, targets := 1 },{ cop := 3, region := 484, targets := 1 },{ cop := 6, region := 289, targets := 128 }], pairs := [(0,7),(2,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 25 146 288 192 448 320), lower := (rows 97 7 44 25 146 288 192 128 256), losses := [] }

theorem u2081 : Upper (D 9) (R 9) [96,5,40,17,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2081 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2082 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 25 146 288 320 192 448), lower := (rows 97 7 44 25 146 288 320 128 256), losses := [] }

theorem u2082 : Upper (D 9) (R 9) [96,5,40,17,130,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2082 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2083 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 3, region := 484, targets := 1 },{ cop := 6, region := 289, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,5),(4,5)], upper := (rows 97 7 44 26 145 288 192 448 320), lower := (rows 97 7 44 26 145 288 192 128 256), losses := [{ target := 7, region := (rows 65 18 28 24 16 371 64 0 321), good := (rows 353 295 44 62 319 288 353 0 288) }] }

theorem u2083 : Upper (D 9) (R 9) [96,5,40,18,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2083 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2084 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 26 145 288 320 192 448), lower := (rows 97 7 44 26 145 288 320 128 256), losses := [] }

theorem u2084 : Upper (D 9) (R 9) [96,5,40,18,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2084 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2085 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 97 7 44 26 208 288 65 384 384), lower := (rows 97 7 44 26 208 288 65 128 256), losses := [] }

theorem u2085 : Upper (D 9) (R 9) [96,5,40,18,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2085 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2086 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 97 7 44 26 208 288 192 385 257), lower := (rows 97 7 44 26 208 288 192 128 256), losses := [] }

theorem u2086 : Upper (D 9) (R 9) [96,5,40,18,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2086 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2087 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 26 208 288 320 129 385), lower := (rows 97 7 44 26 208 288 320 128 256), losses := [] }

theorem u2087 : Upper (D 9) (R 9) [96,5,40,18,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2087 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2088 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 88 145 288 66 384 384), lower := (rows 97 7 44 88 145 288 66 128 256), losses := [] }

theorem u2088 : Upper (D 9) (R 9) [96,5,40,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2088 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2089 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 33 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,5)], upper := (rows 97 7 44 88 145 288 192 386 258), lower := (rows 97 7 44 88 145 288 192 128 256), losses := [] }

theorem u2089 : Upper (D 9) (R 9) [96,5,40,80,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2089 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2090 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 88 145 288 320 130 386), lower := (rows 97 7 44 88 145 288 320 128 256), losses := [] }

theorem u2090 : Upper (D 9) (R 9) [96,5,40,80,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2090 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2091 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,0)], upper := (rows 97 7 44 88 146 288 65 384 384), lower := (rows 97 7 44 88 146 288 65 128 256), losses := [] }

theorem u2091 : Upper (D 9) (R 9) [96,5,40,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2091 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2092 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 33 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,5)], upper := (rows 97 7 44 88 146 288 192 385 257), lower := (rows 97 7 44 88 146 288 192 128 256), losses := [] }

theorem u2092 : Upper (D 9) (R 9) [96,5,40,80,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2092 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2093 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 88 146 288 320 129 385), lower := (rows 97 7 44 88 146 288 320 128 256), losses := [] }

theorem u2093 : Upper (D 9) (R 9) [96,5,40,80,130,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2093 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2094 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 83, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 137 82 288 80 384 384), lower := (rows 97 7 44 137 82 288 80 128 256), losses := [] }

theorem u2094 : Upper (D 9) (R 9) [96,5,40,129,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2094 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2095 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 464, targets := 1 },{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 137 82 288 192 400 272), lower := (rows 97 7 44 137 82 288 192 128 256), losses := [{ target := 8, region := (rows 5 6 4 8 20 32 200 128 0), good := (rows 97 23 127 201 82 32 192 192 0) }] }

theorem u2095 : Upper (D 9) (R 9) [96,5,40,129,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2095 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2096 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 137 82 288 320 144 400), lower := (rows 97 7 44 137 82 288 320 128 256), losses := [] }

theorem u2096 : Upper (D 9) (R 9) [96,5,40,129,66,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2096 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2097 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 464, targets := 1 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 137 146 288 80 448 320), lower := (rows 97 7 44 137 146 288 80 128 256), losses := [] }

theorem u2097 : Upper (D 9) (R 9) [96,5,40,129,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2097 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2098 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 137 146 288 320 208 336), lower := (rows 97 7 44 137 146 288 320 128 256), losses := [] }

theorem u2098 : Upper (D 9) (R 9) [96,5,40,129,130,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2098 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2099 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 137 208 288 66 400 272), lower := (rows 97 7 44 137 208 288 66 128 256), losses := [] }

theorem u2099 : Upper (D 9) (R 9) [96,5,40,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2099 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2099
end Delivery.IrregularNine14.P09
