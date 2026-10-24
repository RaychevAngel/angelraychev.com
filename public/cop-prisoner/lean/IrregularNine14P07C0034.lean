import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0001

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2040 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 7 42 324 88 176 33 192 131 259), lower := (rows 7 42 324 88 176 33 192 128 256), losses := [] }

theorem u2040 : Upper (D 7) (R 7) [6,40,320,80,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2041 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 114, targets := 128 },{ cop := 4, region := 420, targets := 1 }], pairs := [(1,7),(2,0),(4,7)], upper := (rows 7 42 324 137 82 48 65 160 416), lower := (rows 7 42 324 137 82 48 65 128 256), losses := [] }

theorem u2041 : Upper (D 7) (R 7) [6,40,320,129,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2041 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2042 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 42 324 137 82 48 96 129 385), lower := (rows 7 42 324 137 82 48 96 128 256), losses := [] }

theorem u2042 : Upper (D 7) (R 7) [6,40,320,129,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2042 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2043 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 4, region := 293, targets := 128 }], pairs := [(0,7),(1,0),(4,0)], upper := (rows 7 42 324 137 82 48 192 161 289), lower := (rows 7 42 324 137 82 48 192 128 256), losses := [] }

theorem u2043 : Upper (D 7) (R 7) [6,40,320,129,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2043 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2044 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 388, targets := 35 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(2,5)], upper := (rows 7 42 324 137 112 34 65 144 400), lower := (rows 7 42 324 137 112 34 65 128 256), losses := [] }

theorem u2044 : Upper (D 7) (R 7) [6,40,320,129,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2045 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 42 324 137 112 34 80 129 385), lower := (rows 7 42 324 137 112 34 80 128 256), losses := [] }

theorem u2045 : Upper (D 7) (R 7) [6,40,320,129,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2045 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2046 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 324 137 112 34 192 145 273), lower := (rows 7 42 324 137 112 34 192 128 256), losses := [] }

theorem u2046 : Upper (D 7) (R 7) [6,40,320,129,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2047 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,6)], upper := (rows 7 42 324 137 146 96 65 176 304), lower := (rows 7 42 324 137 146 96 65 128 256), losses := [] }

theorem u2047 : Upper (D 7) (R 7) [6,40,320,129,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2048 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(1,0),(4,0)], upper := (rows 7 42 324 137 146 96 80 161 289), lower := (rows 7 42 324 137 146 96 80 128 256), losses := [] }

theorem u2048 : Upper (D 7) (R 7) [6,40,320,129,130,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2048 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2049 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 324 137 146 96 96 145 273), lower := (rows 7 42 324 137 146 96 96 128 256), losses := [] }

theorem u2049 : Upper (D 7) (R 7) [6,40,320,129,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2050 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 3, region := 112, targets := 2 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7),(4,0),(4,1),(4,6)], upper := (rows 7 42 324 137 176 96 65 146 274), lower := (rows 7 42 324 137 176 96 65 128 256), losses := [] }

theorem u2050 : Upper (D 7) (R 7) [6,40,320,129,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2051 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,1),(4,0)], upper := (rows 7 42 324 137 176 96 66 145 273), lower := (rows 7 42 324 137 176 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 19 100 64 137 265), good := (rows 445 440 356 409 176 96 112 128 256) }] }

theorem u2051 : Upper (D 7) (R 7) [6,40,320,129,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2052 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 136, targets := 96 },{ cop := 3, region := 114, targets := 1 }], pairs := [(1,0),(3,5),(3,6)], upper := (rows 7 42 324 137 176 96 80 131 259), lower := (rows 7 42 324 137 176 96 80 128 256), losses := [] }

theorem u2052 : Upper (D 7) (R 7) [6,40,320,129,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2052 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2053 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 3, region := 80, targets := 34 }], pairs := [(1,0),(1,6),(4,1),(4,5)], upper := (rows 7 42 324 137 208 34 65 176 304), lower := (rows 7 42 324 137 208 34 65 128 256), losses := [] }

theorem u2053 : Upper (D 7) (R 7) [6,40,320,129,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2054 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 324 137 208 34 80 161 289), lower := (rows 7 42 324 137 208 34 80 128 256), losses := [] }

theorem u2054 : Upper (D 7) (R 7) [6,40,320,129,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2054 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2055 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 3, region := 34, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 324 137 208 34 96 145 273), lower := (rows 7 42 324 137 208 34 96 128 256), losses := [] }

theorem u2055 : Upper (D 7) (R 7) [6,40,320,129,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2056 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 3, region := 80, targets := 2 }], pairs := [(0,7),(2,7),(4,1)], upper := (rows 7 42 324 137 208 48 65 162 290), lower := (rows 7 42 324 137 208 48 65 128 256), losses := [] }

theorem u2056 : Upper (D 7) (R 7) [6,40,320,129,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2056 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2057 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 3, region := 114, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 7 42 324 137 208 48 66 161 289), lower := (rows 7 42 324 137 208 48 66 128 256), losses := [] }

theorem u2057 : Upper (D 7) (R 7) [6,40,320,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2057 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2058 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 136, targets := 96 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(3,5),(3,6)], upper := (rows 7 42 324 137 208 48 96 131 259), lower := (rows 7 42 324 137 208 48 96 128 256), losses := [] }

theorem u2058 : Upper (D 7) (R 7) [6,40,320,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2058 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2059 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 398, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,0),(2,1),(3,0)], upper := (rows 7 42 324 138 112 33 65 144 400), lower := (rows 7 42 324 138 112 33 65 128 256), losses := [] }

theorem u2059 : Upper (D 7) (R 7) [6,40,320,130,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2060 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 324 138 112 33 80 129 385), lower := (rows 7 42 324 138 112 33 80 128 256), losses := [] }

theorem u2060 : Upper (D 7) (R 7) [6,40,320,130,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2060 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2061 : Route 9 := (fun mask => (mask,id))

def c2061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2061 : Upper (D 7) (R 7) [6,40,320,130,96,1,128] 13 := by
  apply FastRouting.sound _ _ [6,40,320,130,96,1,128] 13 (by decide) (choices 1) [1,16] r2061 c2061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u100
  · exact u101

def r2062 : Route 9 := (fun mask => (mask,id))

def c2062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2062 : Upper (D 7) (R 7) [6,40,320,130,129,64,1] 13 := by
  apply FastRouting.sound _ _ [6,40,320,130,129,64,1] 13 (by decide) (choices 1) [16,32] r2062 c2062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u102
  · exact u103

def b2063 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 324 138 145 96 80 161 289), lower := (rows 7 42 324 138 145 96 80 128 256), losses := [] }

theorem u2063 : Upper (D 7) (R 7) [6,40,320,130,129,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2063 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2064 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 324 138 145 96 96 145 273), lower := (rows 7 42 324 138 145 96 96 128 256), losses := [] }

theorem u2064 : Upper (D 7) (R 7) [6,40,320,130,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2065 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 324 138 208 33 65 176 304), lower := (rows 7 42 324 138 208 33 65 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 97 0 144 272), good := (rows 39 42 292 138 442 33 33 128 256) }] }

theorem u2065 : Upper (D 7) (R 7) [6,40,320,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2066 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 324 138 208 33 80 161 289), lower := (rows 7 42 324 138 208 33 80 128 256), losses := [] }

theorem u2066 : Upper (D 7) (R 7) [6,40,320,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2066 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2067 : Route 9 := (fun mask => (mask,id))

def c2067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2067 : Upper (D 7) (R 7) [6,40,320,130,192,1,32] 13 := by
  apply FastRouting.sound _ _ [6,40,320,130,192,1,32] 13 (by decide) (choices 1) [1,16] r2067 c2067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u104
  · exact u105

def b2068 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 80, targets := 32 },{ cop := 0, region := 80, targets := 128 }], pairs := [(2,0),(2,1),(4,5),(4,7)], upper := (rows 7 42 324 152 82 33 65 160 416), lower := (rows 7 42 324 152 82 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 32 64 162 290), good := (rows 390 426 324 156 478 416 64 128 256) }] }

theorem u2068 : Upper (D 7) (R 7) [6,40,320,144,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2069 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 42 324 152 82 33 96 129 385), lower := (rows 7 42 324 152 82 33 96 128 256), losses := [] }

theorem u2069 : Upper (D 7) (R 7) [6,40,320,144,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2070 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 293, targets := 128 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,7),(2,1),(2,7),(4,0)], upper := (rows 7 42 324 152 82 33 192 161 289), lower := (rows 7 42 324 152 82 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 32 200 128 256), good := (rows 22 122 324 216 82 32 192 192 256) }] }

theorem u2070 : Upper (D 7) (R 7) [6,40,320,144,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2071 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 1 },{ cop := 0, region := 112, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 42 324 152 112 33 65 130 386), lower := (rows 7 42 324 152 112 33 65 128 256), losses := [] }

theorem u2071 : Upper (D 7) (R 7) [6,40,320,144,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2072 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 129 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,7)], upper := (rows 7 42 324 152 112 33 66 129 385), lower := (rows 7 42 324 152 112 33 66 128 256), losses := [] }

theorem u2072 : Upper (D 7) (R 7) [6,40,320,144,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2073 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,1)], upper := (rows 7 42 324 152 112 33 192 131 259), lower := (rows 7 42 324 152 112 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 32 200 128 256), good := (rows 22 122 324 216 112 32 192 192 256) },{ target := 1, region := (rows 1 0 4 8 18 33 200 128 256), good := (rows 53 120 324 216 112 33 192 192 256) }] }

theorem u2073 : Upper (D 7) (R 7) [6,40,320,144,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2074 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 176, targets := 66 }], pairs := [(2,1),(3,0),(4,1),(4,6)], upper := (rows 7 42 324 200 145 33 66 176 304), lower := (rows 7 42 324 200 145 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 67 128 256), good := (rows 70 106 324 200 216 96 66 128 256) },{ target := 1, region := (rows 1 0 68 72 49 49 64 179 307), good := (rows 437 440 332 204 433 433 460 128 256) }] }

theorem u2074 : Upper (D 7) (R 7) [6,40,320,192,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2075 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 324 200 145 33 80 162 290), lower := (rows 7 42 324 200 145 33 80 128 256), losses := [] }

theorem u2075 : Upper (D 7) (R 7) [6,40,320,192,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2075 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2076 : Route 9 := (fun mask => (mask,id))

def c2076 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2076 : Upper (D 7) (R 7) [6,40,320,192,129,1,32] 13 := by
  apply FastRouting.sound _ _ [6,40,320,192,129,1,32] 13 (by decide) (choices 1) [2,16] r2076 c2076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u106
  · exact u107

def b2077 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,6)], upper := (rows 7 42 324 200 146 33 65 176 304), lower := (rows 7 42 324 200 146 33 65 128 256), losses := [] }

theorem u2077 : Upper (D 7) (R 7) [6,40,320,192,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2078 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 324 200 146 33 80 161 289), lower := (rows 7 42 324 200 146 33 80 128 256), losses := [] }

theorem u2078 : Upper (D 7) (R 7) [6,40,320,192,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2078 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2079 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 357, targets := 128 },{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,7),(2,7),(4,5),(4,6)], upper := (rows 7 42 324 200 146 33 96 145 273), lower := (rows 7 42 324 200 146 33 96 128 256), losses := [] }

theorem u2079 : Upper (D 7) (R 7) [6,40,320,192,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2080 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 144, targets := 65 }], pairs := [(2,0),(3,0),(4,0),(4,6)], upper := (rows 7 42 324 200 176 33 65 146 274), lower := (rows 7 42 324 200 176 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 72 50 32 64 131 259), good := (rows 406 442 332 204 176 432 460 128 256) }] }

theorem u2080 : Upper (D 7) (R 7) [6,40,320,192,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2081 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 176, targets := 66 },{ cop := 4, region := 74, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 7 42 324 200 176 33 66 145 273), lower := (rows 7 42 324 200 176 33 66 128 256), losses := [] }

theorem u2081 : Upper (D 7) (R 7) [6,40,320,192,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2082 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 324 200 176 33 80 131 259), lower := (rows 7 42 324 200 176 33 80 128 256), losses := [] }

theorem u2082 : Upper (D 7) (R 7) [6,40,320,192,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2082 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2083 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 56 146 288 65 192 448), lower := (rows 7 98 13 56 146 288 65 128 256), losses := [] }

theorem u2083 : Upper (D 7) (R 7) [6,96,9,48,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2083 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2084 : Route 9 := (fun mask => (mask,id))

def c2084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2084 : Upper (D 7) (R 7) [6,96,9,48,130,256,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48,130,256,128] 13 (by decide) (choices 1) [1,64] r2084 c2084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u108
  · exact u109

def b2085 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 56 208 288 65 130 386), lower := (rows 7 98 13 56 208 288 65 128 256), losses := [] }

theorem u2085 : Upper (D 7) (R 7) [6,96,9,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2085 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2086 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 56 208 288 66 129 385), lower := (rows 7 98 13 56 208 288 66 128 256), losses := [] }

theorem u2086 : Upper (D 7) (R 7) [6,96,9,48,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2086 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2087 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 56 208 288 192 131 259), lower := (rows 7 98 13 56 208 288 192 128 256), losses := [] }

theorem u2087 : Upper (D 7) (R 7) [6,96,9,48,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2087 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2088 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 56 273 160 66 192 448), lower := (rows 7 98 13 56 273 160 66 128 256), losses := [] }

theorem u2088 : Upper (D 7) (R 7) [6,96,9,48,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2089 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 13 56 273 160 192 194 322), lower := (rows 7 98 13 56 273 160 192 128 256), losses := [] }

theorem u2089 : Upper (D 7) (R 7) [6,96,9,48,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2090 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 56 274 160 65 192 448), lower := (rows 7 98 13 56 274 160 65 128 256), losses := [] }

theorem u2090 : Upper (D 7) (R 7) [6,96,9,48,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2091 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 13 56 274 160 192 193 321), lower := (rows 7 98 13 56 274 160 192 128 256), losses := [] }

theorem u2091 : Upper (D 7) (R 7) [6,96,9,48,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2092 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 56 336 160 65 130 386), lower := (rows 7 98 13 56 336 160 65 128 256), losses := [] }

theorem u2092 : Upper (D 7) (R 7) [6,96,9,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2093 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(4,5)], upper := (rows 7 98 13 56 336 160 66 129 385), lower := (rows 7 98 13 56 336 160 66 128 256), losses := [] }

theorem u2093 : Upper (D 7) (R 7) [6,96,9,48,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2094 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 13 56 336 160 192 131 259), lower := (rows 7 98 13 56 336 160 192 128 256), losses := [] }

theorem u2094 : Upper (D 7) (R 7) [6,96,9,48,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2095 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(3,0),(4,0),(4,7)], upper := (rows 7 98 13 152 274 33 192 224 352), lower := (rows 7 98 13 152 274 33 192 128 256), losses := [] }

theorem u2095 : Upper (D 7) (R 7) [6,96,9,144,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2096 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 152 274 96 192 161 289), lower := (rows 7 98 13 152 274 96 192 128 256), losses := [] }

theorem u2096 : Upper (D 7) (R 7) [6,96,9,144,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2097 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 152 304 33 66 192 448), lower := (rows 7 98 13 152 304 33 66 128 256), losses := [] }

theorem u2097 : Upper (D 7) (R 7) [6,96,9,144,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2098 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(3,0),(4,0),(4,7)], upper := (rows 7 98 13 152 304 33 192 194 322), lower := (rows 7 98 13 152 304 33 192 128 256), losses := [] }

theorem u2098 : Upper (D 7) (R 7) [6,96,9,144,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2099 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 152 304 34 65 192 448), lower := (rows 7 98 13 152 304 34 65 128 256), losses := [] }

theorem u2099 : Upper (D 7) (R 7) [6,96,9,144,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2099
end Delivery.IrregularNine14.P07
