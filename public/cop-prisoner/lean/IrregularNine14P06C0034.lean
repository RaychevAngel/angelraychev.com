import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2040 : PairBound 9 := { available := 96, camps := [], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 22 134 104 273 33 68 224 352), lower := (rows 11 22 134 104 273 33 68 128 256), losses := [{ target := 0, region := (rows 0 18 5 40 16 32 119 168 296), good := (rows 462 86 198 488 342 492 68 128 256) }] }

theorem u2040 : Upper (D 6) (R 6) [10,20,130,96,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2041 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 134 104 273 33 96 196 324), lower := (rows 11 22 134 104 273 33 96 128 256), losses := [] }

theorem u2041 : Upper (D 6) (R 6) [10,20,130,96,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2042 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 134 104 273 36 96 193 321), lower := (rows 11 22 134 104 273 36 96 128 256), losses := [] }

theorem u2042 : Upper (D 6) (R 6) [10,20,130,96,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2043 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 134 104 304 33 65 196 324), lower := (rows 11 22 134 104 304 33 65 128 256), losses := [] }

theorem u2043 : Upper (D 6) (R 6) [10,20,130,96,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2044 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 22 134 104 304 33 68 193 321), lower := (rows 11 22 134 104 304 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 49 33 70 129 257), good := (rows 505 84 196 120 304 441 68 128 256) }] }

theorem u2044 : Upper (D 6) (R 6) [10,20,130,96,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2045 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 134 265 112 33 68 224 352), lower := (rows 11 22 134 265 112 33 68 128 256), losses := [] }

theorem u2045 : Upper (D 6) (R 6) [10,20,130,257,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2046 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 134 265 112 36 96 193 321), lower := (rows 11 22 134 265 112 36 96 128 256), losses := [] }

theorem u2046 : Upper (D 6) (R 6) [10,20,130,257,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2047 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 22 134 268 112 33 65 224 352), lower := (rows 11 22 134 268 112 33 65 128 256), losses := [] }

theorem u2047 : Upper (D 6) (R 6) [10,20,130,260,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2048 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 22 134 268 112 33 96 193 321), lower := (rows 11 22 134 268 112 33 96 128 256), losses := [] }

theorem u2048 : Upper (D 6) (R 6) [10,20,130,260,96,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2049 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(4,1),(4,2)], upper := (rows 11 22 134 296 49 96 65 196 324), lower := (rows 11 22 134 296 49 96 65 128 256), losses := [] }

theorem u2049 : Upper (D 6) (R 6) [10,20,130,288,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2050 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(3,1)], upper := (rows 11 22 134 296 49 96 68 193 321), lower := (rows 11 22 134 296 49 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 25 17 103 70 129 257), good := (rows 505 124 228 296 441 96 100 128 256) }] }

theorem u2050 : Upper (D 6) (R 6) [10,20,130,288,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2051 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 296, targets := 6 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 22 134 296 81 33 68 224 352), lower := (rows 11 22 134 296 81 33 68 128 256), losses := [{ target := 0, region := (rows 0 18 5 40 16 32 119 168 296), good := (rows 462 86 198 488 86 492 68 128 256) }] }

theorem u2051 : Upper (D 6) (R 6) [10,20,130,288,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2052 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 134, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 22 134 296 81 33 96 196 324), lower := (rows 11 22 134 296 81 33 96 128 256), losses := [] }

theorem u2052 : Upper (D 6) (R 6) [10,20,130,288,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2053 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 22 134 296 81 36 65 224 352), lower := (rows 11 22 134 296 81 36 65 128 256), losses := [] }

theorem u2053 : Upper (D 6) (R 6) [10,20,130,288,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2054 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 134, targets := 32 }], pairs := [(1,5),(2,5),(3,1)], upper := (rows 11 22 134 296 81 36 96 193 321), lower := (rows 11 22 134 296 81 36 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 11 17 38 111 145 273), good := (rows 505 508 236 360 473 100 96 128 256) }] }

theorem u2054 : Upper (D 6) (R 6) [10,20,130,288,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2055 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 22 134 296 81 96 65 164 292), lower := (rows 11 22 134 296 81 96 65 128 256), losses := [] }

theorem u2055 : Upper (D 6) (R 6) [10,20,130,288,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2056 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 296, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 11 22 134 296 81 96 68 161 289), lower := (rows 11 22 134 296 81 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 27 17 119 70 145 273), good := (rows 505 508 236 296 505 96 100 128 256) }] }

theorem u2056 : Upper (D 6) (R 6) [10,20,130,288,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2057 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 134, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 11 22 134 296 81 96 96 133 261), lower := (rows 11 22 134 296 81 96 96 128 256), losses := [] }

theorem u2057 : Upper (D 6) (R 6) [10,20,130,288,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2058 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 22 134 296 112 33 65 196 324), lower := (rows 11 22 134 296 112 33 65 128 256), losses := [] }

theorem u2058 : Upper (D 6) (R 6) [10,20,130,288,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2059 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 22 134 296 112 33 68 193 321), lower := (rows 11 22 134 296 112 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 41 17 33 70 129 257), good := (rows 505 84 196 296 120 441 68 128 256) }] }

theorem u2059 : Upper (D 6) (R 6) [10,20,130,288,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2060 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 41 274 96 65 196 324), lower := (rows 11 22 164 41 274 96 65 128 256), losses := [] }

theorem u2060 : Upper (D 6) (R 6) [10,20,160,33,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2061 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 22 164 41 274 96 68 193 321), lower := (rows 11 22 164 41 274 96 68 128 256), losses := [] }

theorem u2061 : Upper (D 6) (R 6) [10,20,160,33,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2062 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 73 273 96 66 164 292), lower := (rows 11 22 164 73 273 96 66 128 256), losses := [] }

theorem u2062 : Upper (D 6) (R 6) [10,20,160,65,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2063 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 4, region := 230, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 22 164 73 273 96 68 162 290), lower := (rows 11 22 164 73 273 96 68 128 256), losses := [] }

theorem u2063 : Upper (D 6) (R 6) [10,20,160,65,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2064 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 22 164 73 273 96 96 134 262), lower := (rows 11 22 164 73 273 96 96 128 256), losses := [] }

theorem u2064 : Upper (D 6) (R 6) [10,20,160,65,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2065 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 164 73 274 96 65 164 292), lower := (rows 11 22 164 73 274 96 65 128 256), losses := [] }

theorem u2065 : Upper (D 6) (R 6) [10,20,160,65,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2066 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(2,1),(3,1)], upper := (rows 11 22 164 73 274 96 68 161 289), lower := (rows 11 22 164 73 274 96 68 128 256), losses := [] }

theorem u2066 : Upper (D 6) (R 6) [10,20,160,65,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2067 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 11 22 164 73 274 96 96 133 261), lower := (rows 11 22 164 73 274 96 96 128 256), losses := [] }

theorem u2067 : Upper (D 6) (R 6) [10,20,160,65,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2068 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 73 304 34 65 196 324), lower := (rows 11 22 164 73 304 34 65 128 256), losses := [] }

theorem u2068 : Upper (D 6) (R 6) [10,20,160,65,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2069 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,1),(3,5)], upper := (rows 11 22 164 73 304 34 68 193 321), lower := (rows 11 22 164 73 304 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 32 70 137 265), good := (rows 457 84 228 457 304 96 68 128 256) }] }

theorem u2069 : Upper (D 6) (R 6) [10,20,160,65,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2070 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 164 73 304 96 65 134 262), lower := (rows 11 22 164 73 304 96 65 128 256), losses := [] }

theorem u2070 : Upper (D 6) (R 6) [10,20,160,65,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2071 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 1, region := 73, targets := 32 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 22 164 73 304 96 66 133 261), lower := (rows 11 22 164 73 304 96 66 128 256), losses := [] }

theorem u2071 : Upper (D 6) (R 6) [10,20,160,65,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2072 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 7, region := 100, targets := 1 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 22 164 73 304 96 68 131 259), lower := (rows 11 22 164 73 304 96 68 128 256), losses := [] }

theorem u2072 : Upper (D 6) (R 6) [10,20,160,65,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2073 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 166, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 164 73 336 34 65 164 292), lower := (rows 11 22 164 73 336 34 65 128 256), losses := [] }

theorem u2073 : Upper (D 6) (R 6) [10,20,160,65,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2074 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 164, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 22 164 73 336 34 68 161 289), lower := (rows 11 22 164 73 336 34 68 128 256), losses := [] }

theorem u2074 : Upper (D 6) (R 6) [10,20,160,65,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2075 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 0, region := 164, targets := 64 }], pairs := [(0,2),(2,6),(3,2)], upper := (rows 11 22 164 73 336 34 96 133 261), lower := (rows 11 22 164 73 336 34 96 128 256), losses := [] }

theorem u2075 : Upper (D 6) (R 6) [10,20,160,65,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2076 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 164 76 273 33 66 224 352), lower := (rows 11 22 164 76 273 33 66 128 256), losses := [] }

theorem u2076 : Upper (D 6) (R 6) [10,20,160,68,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2077 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 164 76 273 33 96 194 322), lower := (rows 11 22 164 76 273 33 96 128 256), losses := [] }

theorem u2077 : Upper (D 6) (R 6) [10,20,160,68,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2078 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 164 76 273 34 65 224 352), lower := (rows 11 22 164 76 273 34 65 128 256), losses := [] }

theorem u2078 : Upper (D 6) (R 6) [10,20,160,68,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2079 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 164 76 273 34 96 193 321), lower := (rows 11 22 164 76 273 34 96 128 256), losses := [] }

theorem u2079 : Upper (D 6) (R 6) [10,20,160,68,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2080 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 164 76 273 96 65 162 290), lower := (rows 11 22 164 76 273 96 65 128 256), losses := [] }

theorem u2080 : Upper (D 6) (R 6) [10,20,160,68,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2081 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 164 76 273 96 66 161 289), lower := (rows 11 22 164 76 273 96 66 128 256), losses := [] }

theorem u2081 : Upper (D 6) (R 6) [10,20,160,68,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2082 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 275, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 22 164 76 273 96 96 131 259), lower := (rows 11 22 164 76 273 96 96 128 256), losses := [] }

theorem u2082 : Upper (D 6) (R 6) [10,20,160,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2083 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 164 76 336 33 65 162 290), lower := (rows 11 22 164 76 336 33 65 128 256), losses := [] }

theorem u2083 : Upper (D 6) (R 6) [10,20,160,68,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2084 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 164, targets := 66 },{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(2,1),(2,6)], upper := (rows 11 22 164 76 336 33 66 161 289), lower := (rows 11 22 164 76 336 33 66 128 256), losses := [] }

theorem u2084 : Upper (D 6) (R 6) [10,20,160,68,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2085 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 164 76 336 33 96 131 259), lower := (rows 11 22 164 76 336 33 96 128 256), losses := [] }

theorem u2085 : Upper (D 6) (R 6) [10,20,160,68,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2086 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 164 76 336 34 65 161 289), lower := (rows 11 22 164 76 336 34 65 128 256), losses := [] }

theorem u2086 : Upper (D 6) (R 6) [10,20,160,68,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2087 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 164 76 336 34 96 129 257), lower := (rows 11 22 164 76 336 34 96 128 256), losses := [] }

theorem u2087 : Upper (D 6) (R 6) [10,20,160,68,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2088 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 3, region := 132, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 22 164 104 273 33 66 196 324), lower := (rows 11 22 164 104 273 33 66 128 256), losses := [] }

theorem u2088 : Upper (D 6) (R 6) [10,20,160,96,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2089 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 22 164 104 273 33 68 194 322), lower := (rows 11 22 164 104 273 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 16 32 110 131 259), good := (rows 458 478 236 108 400 492 76 128 256) }] }

theorem u2089 : Upper (D 6) (R 6) [10,20,160,96,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2090 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 3, region := 132, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 22 164 104 273 34 65 196 324), lower := (rows 11 22 164 104 273 34 65 128 256), losses := [] }

theorem u2090 : Upper (D 6) (R 6) [10,20,160,96,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2091 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 22 164 104 273 34 68 193 321), lower := (rows 11 22 164 104 273 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 44 17 32 70 129 257), good := (rows 473 92 236 104 401 104 76 128 256) }] }

theorem u2091 : Upper (D 6) (R 6) [10,20,160,96,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2092 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 104 274 33 65 196 324), lower := (rows 11 22 164 104 274 33 65 128 256), losses := [] }

theorem u2092 : Upper (D 6) (R 6) [10,20,160,96,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2093 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 72, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 22 164 104 274 33 68 193 321), lower := (rows 11 22 164 104 274 33 68 128 256), losses := [] }

theorem u2093 : Upper (D 6) (R 6) [10,20,160,96,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2094 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 164 104 336 33 65 134 262), lower := (rows 11 22 164 104 336 33 65 128 256), losses := [] }

theorem u2094 : Upper (D 6) (R 6) [10,20,160,96,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2095 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 164, targets := 66 },{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 11 22 164 104 336 33 66 133 261), lower := (rows 11 22 164 104 336 33 66 128 256), losses := [] }

theorem u2095 : Upper (D 6) (R 6) [10,20,160,96,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2096 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 22 164 104 336 33 68 131 259), lower := (rows 11 22 164 104 336 33 68 128 256), losses := [] }

theorem u2096 : Upper (D 6) (R 6) [10,20,160,96,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2097 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 0, region := 164, targets := 64 }], pairs := [(0,2),(2,6),(3,2)], upper := (rows 11 22 164 104 336 34 65 133 261), lower := (rows 11 22 164 104 336 34 65 128 256), losses := [] }

theorem u2097 : Upper (D 6) (R 6) [10,20,160,96,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2098 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 22 164 104 336 34 68 129 257), lower := (rows 11 22 164 104 336 34 68 128 256), losses := [] }

theorem u2098 : Upper (D 6) (R 6) [10,20,160,96,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2099 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 22 164 265 81 96 66 164 292), lower := (rows 11 22 164 265 81 96 66 128 256), losses := [] }

theorem u2099 : Upper (D 6) (R 6) [10,20,160,257,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2099
end Delivery.IrregularNine14.P06
