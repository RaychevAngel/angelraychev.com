import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0004

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2040 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 35 70 44 137 112 48 449 385 385), lower := (rows 35 70 44 137 112 48 64 128 256), losses := [] }

theorem u2040 : Upper (D 8) (R 8) [34,68,40,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2040 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2041 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 137 112 160 337 401 273), lower := (rows 35 70 44 137 112 160 64 128 256), losses := [] }

theorem u2041 : Upper (D 8) (R 8) [34,68,40,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2042 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 70 44 137 112 288 209 145 401), lower := (rows 35 70 44 137 112 288 64 128 256), losses := [] }

theorem u2042 : Upper (D 8) (R 8) [34,68,40,129,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2042 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2043 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 137 176 33 336 464 336), lower := (rows 35 70 44 137 176 33 64 128 256), losses := [] }

theorem u2043 : Upper (D 8) (R 8) [34,68,40,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2044 : PairBound 9 := { available := 321, camps := [], pairs := [], upper := (rows 35 70 44 137 176 48 321 449 321), lower := (rows 35 70 44 137 176 48 64 128 256), losses := [] }

theorem u2044 : Upper (D 8) (R 8) [34,68,40,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2044 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2045 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 137 176 96 337 401 273), lower := (rows 35 70 44 137 176 96 64 128 256), losses := [] }

theorem u2045 : Upper (D 8) (R 8) [34,68,40,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2046 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 70 44 137 176 288 81 209 337), lower := (rows 35 70 44 137 176 288 64 128 256), losses := [] }

theorem u2046 : Upper (D 8) (R 8) [34,68,40,129,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2046 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2047 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 137 208 33 368 432 304), lower := (rows 35 70 44 137 208 33 64 128 256), losses := [] }

theorem u2047 : Upper (D 8) (R 8) [34,68,40,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2048 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 35 70 44 137 208 48 353 417 289), lower := (rows 35 70 44 137 208 48 64 128 256), losses := [] }

theorem u2048 : Upper (D 8) (R 8) [34,68,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2048 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2049 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 70 44 137 208 288 113 177 305), lower := (rows 35 70 44 137 208 288 64 128 256), losses := [] }

theorem u2049 : Upper (D 8) (R 8) [34,68,40,129,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2049 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2050 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 70 44 137 273 48 224 224 480), lower := (rows 35 70 44 137 273 48 64 128 256), losses := [] }

theorem u2050 : Upper (D 8) (R 8) [34,68,40,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2050 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2051 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 137 273 96 240 176 432), lower := (rows 35 70 44 137 273 96 64 128 256), losses := [] }

theorem u2051 : Upper (D 8) (R 8) [34,68,40,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2052 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 137 273 160 112 240 368), lower := (rows 35 70 44 137 273 160 64 128 256), losses := [] }

theorem u2052 : Upper (D 8) (R 8) [34,68,40,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2053 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 137 304 33 208 208 464), lower := (rows 35 70 44 137 304 33 64 128 256), losses := [] }

theorem u2053 : Upper (D 8) (R 8) [34,68,40,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2054 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 70 44 137 304 48 193 193 449), lower := (rows 35 70 44 137 304 48 64 128 256), losses := [] }

theorem u2054 : Upper (D 8) (R 8) [34,68,40,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2054 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2055 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 137 304 96 209 145 401), lower := (rows 35 70 44 137 304 96 64 128 256), losses := [] }

theorem u2055 : Upper (D 8) (R 8) [34,68,40,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2056 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 137 304 160 81 209 337), lower := (rows 35 70 44 137 304 160 64 128 256), losses := [] }

theorem u2056 : Upper (D 8) (R 8) [34,68,40,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2057 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 137 336 33 240 176 432), lower := (rows 35 70 44 137 336 33 64 128 256), losses := [] }

theorem u2057 : Upper (D 8) (R 8) [34,68,40,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2058 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 44 137 336 48 225 161 417), lower := (rows 35 70 44 137 336 48 64 128 256), losses := [] }

theorem u2058 : Upper (D 8) (R 8) [34,68,40,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2058 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2059 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 137 336 160 113 177 305), lower := (rows 35 70 44 137 336 160 64 128 256), losses := [] }

theorem u2059 : Upper (D 8) (R 8) [34,68,40,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2060 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 137 400 33 112 240 368), lower := (rows 35 70 44 137 400 33 64 128 256), losses := [] }

theorem u2060 : Upper (D 8) (R 8) [34,68,40,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2061 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 44 137 400 48 97 225 353), lower := (rows 35 70 44 137 400 48 64 128 256), losses := [] }

theorem u2061 : Upper (D 8) (R 8) [34,68,40,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2061 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2062 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 137 400 96 113 177 305), lower := (rows 35 70 44 137 400 96 64 128 256), losses := [] }

theorem u2062 : Upper (D 8) (R 8) [34,68,40,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2063 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 152 273 33 224 224 480), lower := (rows 35 70 44 152 273 33 64 128 256), losses := [] }

theorem u2063 : Upper (D 8) (R 8) [34,68,40,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2064 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 152 273 96 225 161 417), lower := (rows 35 70 44 152 273 96 64 128 256), losses := [] }

theorem u2064 : Upper (D 8) (R 8) [34,68,40,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2065 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 152 273 160 97 225 353), lower := (rows 35 70 44 152 273 160 64 128 256), losses := [] }

theorem u2065 : Upper (D 8) (R 8) [34,68,40,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2066 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 152 304 33 193 193 449), lower := (rows 35 70 44 152 304 33 64 128 256), losses := [] }

theorem u2066 : Upper (D 8) (R 8) [34,68,40,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2067 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 152 304 96 193 129 385), lower := (rows 35 70 44 152 304 96 64 128 256), losses := [] }

theorem u2067 : Upper (D 8) (R 8) [34,68,40,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2068 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 152 304 160 65 193 321), lower := (rows 35 70 44 152 304 160 64 128 256), losses := [] }

theorem u2068 : Upper (D 8) (R 8) [34,68,40,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2069 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 265 112 33 208 144 400), lower := (rows 35 70 44 265 112 33 64 128 256), losses := [] }

theorem u2069 : Upper (D 8) (R 8) [34,68,40,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2070 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 44 265 112 48 193 129 385), lower := (rows 35 70 44 265 112 48 64 128 256), losses := [] }

theorem u2070 : Upper (D 8) (R 8) [34,68,40,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2070 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2071 : Route 9 := (fun mask => (mask,id))

def c2071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2071 : Upper (D 8) (R 8) [34,68,40,257,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,96,128] 13 (by decide) (choices 1) [1,16,128] r2071 c2071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u279
  · exact u280
  · exact u281

def b2072 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 70 44 265 145 48 224 224 480), lower := (rows 35 70 44 265 145 48 64 128 256), losses := [] }

theorem u2072 : Upper (D 8) (R 8) [34,68,40,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2072 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2073 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 265 145 96 240 176 432), lower := (rows 35 70 44 265 145 96 64 128 256), losses := [] }

theorem u2073 : Upper (D 8) (R 8) [34,68,40,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2074 : Route 9 := (fun mask => (mask,id))

def c2074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2074 : Upper (D 8) (R 8) [34,68,40,257,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,129,128] 13 (by decide) (choices 1) [16,32] r2074 c2074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u282
  · exact u283

def b2075 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 265 176 33 208 208 464), lower := (rows 35 70 44 265 176 33 64 128 256), losses := [] }

theorem u2075 : Upper (D 8) (R 8) [34,68,40,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2076 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 70 44 265 176 48 193 193 449), lower := (rows 35 70 44 265 176 48 64 128 256), losses := [] }

theorem u2076 : Upper (D 8) (R 8) [34,68,40,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2076 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2077 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 265 176 96 209 145 401), lower := (rows 35 70 44 265 176 96 64 128 256), losses := [] }

theorem u2077 : Upper (D 8) (R 8) [34,68,40,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2078 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 265 176 160 81 209 337), lower := (rows 35 70 44 265 176 160 64 128 256), losses := [] }

theorem u2078 : Upper (D 8) (R 8) [34,68,40,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2079 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 265 208 33 240 176 432), lower := (rows 35 70 44 265 208 33 64 128 256), losses := [] }

theorem u2079 : Upper (D 8) (R 8) [34,68,40,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2080 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 44 265 208 48 225 161 417), lower := (rows 35 70 44 265 208 48 64 128 256), losses := [] }

theorem u2080 : Upper (D 8) (R 8) [34,68,40,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2080 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2081 : Route 9 := (fun mask => (mask,id))

def c2081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2081 : Upper (D 8) (R 8) [34,68,40,257,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,192,128] 13 (by decide) (choices 1) [1,16,32] r2081 c2081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u284
  · exact u285
  · exact u286

def b2082 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 280 145 33 224 224 480), lower := (rows 35 70 44 280 145 33 64 128 256), losses := [] }

theorem u2082 : Upper (D 8) (R 8) [34,68,40,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2083 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 280 145 96 225 161 417), lower := (rows 35 70 44 280 145 96 64 128 256), losses := [] }

theorem u2083 : Upper (D 8) (R 8) [34,68,40,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2084 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 280 145 160 97 225 353), lower := (rows 35 70 44 280 145 160 64 128 256), losses := [] }

theorem u2084 : Upper (D 8) (R 8) [34,68,40,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2085 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 280 176 33 193 193 449), lower := (rows 35 70 44 280 176 33 64 128 256), losses := [] }

theorem u2085 : Upper (D 8) (R 8) [34,68,40,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2086 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 280 176 96 193 129 385), lower := (rows 35 70 44 280 176 96 64 128 256), losses := [] }

theorem u2086 : Upper (D 8) (R 8) [34,68,40,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2087 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 280 176 160 65 193 321), lower := (rows 35 70 44 280 176 160 64 128 256), losses := [] }

theorem u2087 : Upper (D 8) (R 8) [34,68,40,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2088 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 392 112 33 209 145 401), lower := (rows 35 70 44 392 112 33 64 128 256), losses := [] }

theorem u2088 : Upper (D 8) (R 8) [34,68,40,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2089 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 44 392 112 48 193 129 385), lower := (rows 35 70 44 392 112 48 64 128 256), losses := [] }

theorem u2089 : Upper (D 8) (R 8) [34,68,40,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2089 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2090 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 83, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 392 112 160 81 145 273), lower := (rows 35 70 44 392 112 160 64 128 256), losses := [] }

theorem u2090 : Upper (D 8) (R 8) [34,68,40,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2091 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 392 145 33 112 240 368), lower := (rows 35 70 44 392 145 33 64 128 256), losses := [] }

theorem u2091 : Upper (D 8) (R 8) [34,68,40,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2092 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 44 392 145 48 97 225 353), lower := (rows 35 70 44 392 145 48 64 128 256), losses := [] }

theorem u2092 : Upper (D 8) (R 8) [34,68,40,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2092 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2093 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 392 145 96 113 177 305), lower := (rows 35 70 44 392 145 96 64 128 256), losses := [] }

theorem u2093 : Upper (D 8) (R 8) [34,68,40,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2094 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 392 176 33 81 209 337), lower := (rows 35 70 44 392 176 33 64 128 256), losses := [] }

theorem u2094 : Upper (D 8) (R 8) [34,68,40,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2095 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 70 44 392 176 48 65 193 321), lower := (rows 35 70 44 392 176 48 64 128 256), losses := [] }

theorem u2095 : Upper (D 8) (R 8) [34,68,40,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2095 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2096 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 392 176 96 81 145 273), lower := (rows 35 70 44 392 176 96 64 128 256), losses := [] }

theorem u2096 : Upper (D 8) (R 8) [34,68,40,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2097 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 392 208 33 113 177 305), lower := (rows 35 70 44 392 208 33 64 128 256), losses := [] }

theorem u2097 : Upper (D 8) (R 8) [34,68,40,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2098 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 44 392 208 48 97 161 289), lower := (rows 35 70 44 392 208 48 64 128 256), losses := [] }

theorem u2098 : Upper (D 8) (R 8) [34,68,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2098 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2099 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 56 208 33 360 424 296), lower := (rows 35 70 133 56 208 33 64 128 256), losses := [] }

theorem u2099 : Upper (D 8) (R 8) [34,68,129,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2099
end Delivery.IrregularNine14.P08
