import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0008

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7020 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 21 266 208 34 192 161 289), lower := (rows 37 74 21 266 208 34 192 128 256), losses := [] }

theorem u7020 : Upper (D 7) (R 7) [36,72,17,258,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7021 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 37 74 21 296 208 34 65 130 386), lower := (rows 37 74 21 296 208 34 65 128 256), losses := [] }

theorem u7021 : Upper (D 7) (R 7) [36,72,17,288,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7022 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 21 296 208 34 66 129 385), lower := (rows 37 74 21 296 208 34 66 128 256), losses := [] }

theorem u7022 : Upper (D 7) (R 7) [36,72,17,288,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7023 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 21 296 208 34 192 131 259), lower := (rows 37 74 21 296 208 34 192 128 256), losses := [] }

theorem u7023 : Upper (D 7) (R 7) [36,72,17,288,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7024 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 424, targets := 64 }], pairs := [(1,0),(3,0),(3,6),(4,0)], upper := (rows 37 74 21 392 208 34 65 162 290), lower := (rows 37 74 21 392 208 34 65 128 256), losses := [] }

theorem u7024 : Upper (D 7) (R 7) [36,72,17,384,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7025 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 3, region := 82, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(4,0)], upper := (rows 37 74 21 392 208 34 66 161 289), lower := (rows 37 74 21 392 208 34 66 128 256), losses := [] }

theorem u7025 : Upper (D 7) (R 7) [36,72,17,384,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7026 : Route 9 := (fun mask => (mask,id))

def c7026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7026 : Upper (D 7) (R 7) [36,72,17,384,192,2,32] 13 := by
  apply FastRouting.sound _ _ [36,72,17,384,192,2,32] 13 (by decide) (choices 1) [1,2] r7026 c7026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u514
  · exact u515

def b7027 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 74 22 42 273 160 65 192 448), lower := (rows 37 74 22 42 273 160 65 128 256), losses := [] }

theorem u7027 : Upper (D 7) (R 7) [36,72,18,34,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7028 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 5, region := 74, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 22 42 273 160 192 193 321), lower := (rows 37 74 22 42 273 160 192 128 256), losses := [] }

theorem u7028 : Upper (D 7) (R 7) [36,72,18,34,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7029 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 86, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 37 74 22 137 81 160 66 416 288), lower := (rows 37 74 22 137 81 160 66 128 256), losses := [] }

theorem u7029 : Upper (D 7) (R 7) [36,72,18,129,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7030 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 74 22 137 81 160 96 386 258), lower := (rows 37 74 22 137 81 160 96 128 256), losses := [] }

theorem u7030 : Upper (D 7) (R 7) [36,72,18,129,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7031 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 169, targets := 64 },{ cop := 3, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 37 74 22 137 81 160 320 162 290), lower := (rows 37 74 22 137 81 160 320 128 256), losses := [] }

theorem u7031 : Upper (D 7) (R 7) [36,72,18,129,65,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7031 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7032 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 22 137 273 96 66 160 416), lower := (rows 37 74 22 137 273 96 66 128 256), losses := [] }

theorem u7032 : Upper (D 7) (R 7) [36,72,18,129,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7033 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 3, region := 98, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(1,7)], upper := (rows 37 74 22 137 273 96 96 130 386), lower := (rows 37 74 22 137 273 96 96 128 256), losses := [] }

theorem u7033 : Upper (D 7) (R 7) [36,72,18,129,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7034 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 22 137 273 96 192 162 290), lower := (rows 37 74 22 137 273 96 192 128 256), losses := [] }

theorem u7034 : Upper (D 7) (R 7) [36,72,18,129,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7035 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 66, targets := 160 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 74 22 137 273 160 66 224 352), lower := (rows 37 74 22 137 273 160 66 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 20 238 64 194 322), good := (rows 61 488 445 169 273 160 480 160 256) }] }

theorem u7035 : Upper (D 7) (R 7) [36,72,18,129,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7036 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(4,7)], upper := (rows 37 74 22 137 273 160 96 194 322), lower := (rows 37 74 22 137 273 160 96 128 256), losses := [{ target := 7, region := (rows 1 10 14 8 24 32 97 0 266), good := (rows 101 350 278 351 337 96 96 0 256) }] }

theorem u7036 : Upper (D 7) (R 7) [36,72,18,129,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7037 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 1, region := 436, targets := 1 }], pairs := [(1,5),(2,0),(3,5),(4,0)], upper := (rows 37 74 22 137 304 160 65 194 322), lower := (rows 37 74 22 137 304 160 65 128 256), losses := [] }

theorem u7037 : Upper (D 7) (R 7) [36,72,18,129,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7038 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 3, region := 66, targets := 1 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(3,5)], upper := (rows 37 74 22 137 304 160 66 193 321), lower := (rows 37 74 22 137 304 160 66 128 256), losses := [] }

theorem u7038 : Upper (D 7) (R 7) [36,72,18,129,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7039 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 436, targets := 1 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,6),(2,0),(3,6),(4,0)], upper := (rows 37 74 22 137 336 160 65 162 290), lower := (rows 37 74 22 137 336 160 65 128 256), losses := [] }

theorem u7039 : Upper (D 7) (R 7) [36,72,18,129,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7040 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 169, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 22 137 336 160 66 161 289), lower := (rows 37 74 22 137 336 160 66 128 256), losses := [] }

theorem u7040 : Upper (D 7) (R 7) [36,72,18,129,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7041 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 169, targets := 64 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,6),(1,0),(1,7),(3,6)], upper := (rows 37 74 22 137 336 160 96 131 259), lower := (rows 37 74 22 137 336 160 96 128 256), losses := [{ target := 7, region := (rows 1 10 14 8 26 32 97 0 264), good := (rows 101 350 22 351 336 96 96 0 256) }] }

theorem u7041 : Upper (D 7) (R 7) [36,72,18,129,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7042 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 436, targets := 1 },{ cop := 2, region := 97, targets := 2 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(2,0),(4,0)], upper := (rows 37 74 22 137 400 96 65 162 290), lower := (rows 37 74 22 137 400 96 65 128 256), losses := [] }

theorem u7042 : Upper (D 7) (R 7) [36,72,18,129,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7043 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 22 137 400 96 66 161 289), lower := (rows 37 74 22 137 400 96 66 128 256), losses := [] }

theorem u7043 : Upper (D 7) (R 7) [36,72,18,129,384,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7044 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 97, targets := 2 },{ cop := 2, region := 97, targets := 128 },{ cop := 3, region := 98, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(1,7)], upper := (rows 37 74 22 137 400 96 96 131 259), lower := (rows 37 74 22 137 400 96 96 128 256), losses := [] }

theorem u7044 : Upper (D 7) (R 7) [36,72,18,129,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7045 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 6, region := 170, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 22 138 273 160 65 224 352), lower := (rows 37 74 22 138 273 160 65 128 256), losses := [] }

theorem u7045 : Upper (D 7) (R 7) [36,72,18,130,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7046 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 5, region := 74, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 22 138 273 160 96 193 321), lower := (rows 37 74 22 138 273 160 96 128 256), losses := [] }

theorem u7046 : Upper (D 7) (R 7) [36,72,18,130,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7047 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 22 168 81 288 65 130 386), lower := (rows 37 74 22 168 81 288 65 128 256), losses := [] }

theorem u7047 : Upper (D 7) (R 7) [36,72,18,160,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7047 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7048 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 74 22 168 81 288 66 129 385), lower := (rows 37 74 22 168 81 288 66 128 256), losses := [] }

theorem u7048 : Upper (D 7) (R 7) [36,72,18,160,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7048 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7049 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 22 168 81 288 192 131 259), lower := (rows 37 74 22 168 81 288 192 128 256), losses := [] }

theorem u7049 : Upper (D 7) (R 7) [36,72,18,160,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7049 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7050 : PairBound 9 := { available := 258, camps := [{ cop := 5, region := 394, targets := 1 },{ cop := 2, region := 97, targets := 2 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 37 74 22 168 145 96 65 386 258), lower := (rows 37 74 22 168 145 96 65 128 256), losses := [] }

theorem u7050 : Upper (D 7) (R 7) [36,72,18,160,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7051 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 22 168 145 96 66 385 257), lower := (rows 37 74 22 168 145 96 66 128 256), losses := [] }

theorem u7051 : Upper (D 7) (R 7) [36,72,18,160,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7052 : Route 9 := (fun mask => (mask,id))

def c7052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7052 : Upper (D 7) (R 7) [36,72,18,160,129,64,256] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,129,64,256] 13 (by decide) (choices 1) [1,2] r7052 c7052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u516
  · exact u517

def b7053 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 426, targets := 1 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,0),(3,0)], upper := (rows 37 74 22 168 145 288 65 194 322), lower := (rows 37 74 22 168 145 288 65 128 256), losses := [] }

theorem u7053 : Upper (D 7) (R 7) [36,72,18,160,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7053 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7054 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 22 168 145 288 66 193 321), lower := (rows 37 74 22 168 145 288 66 128 256), losses := [] }

theorem u7054 : Upper (D 7) (R 7) [36,72,18,160,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7054 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7055 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 5, region := 138, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 37 74 22 168 273 96 65 130 386), lower := (rows 37 74 22 168 273 96 65 128 256), losses := [] }

theorem u7055 : Upper (D 7) (R 7) [36,72,18,160,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7056 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 22 168 273 96 66 129 385), lower := (rows 37 74 22 168 273 96 66 128 256), losses := [] }

theorem u7056 : Upper (D 7) (R 7) [36,72,18,160,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7057 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 6, region := 42, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 22 168 273 96 192 131 259), lower := (rows 37 74 22 168 273 96 192 128 256), losses := [] }

theorem u7057 : Upper (D 7) (R 7) [36,72,18,160,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7058 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 74 22 168 400 33 65 194 322), lower := (rows 37 74 22 168 400 33 65 128 256), losses := [] }

theorem u7058 : Upper (D 7) (R 7) [36,72,18,160,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7059 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 161 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 74 22 168 400 33 66 193 321), lower := (rows 37 74 22 168 400 33 66 128 256), losses := [] }

theorem u7059 : Upper (D 7) (R 7) [36,72,18,160,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7060 : Route 9 := (fun mask => (mask,id))

def c7060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7060 : Upper (D 7) (R 7) [36,72,18,160,384,64,1] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,384,64,1] 13 (by decide) (choices 1) [1,2] r7060 c7060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u518
  · exact u519

def b7061 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 22 168 400 96 66 129 257), lower := (rows 37 74 22 168 400 96 66 128 256), losses := [] }

theorem u7061 : Upper (D 7) (R 7) [36,72,18,160,384,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7062 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 86, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 37 74 22 265 81 160 66 160 416), lower := (rows 37 74 22 265 81 160 66 128 256), losses := [] }

theorem u7062 : Upper (D 7) (R 7) [36,72,18,257,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7063 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 74 22 265 81 160 96 130 386), lower := (rows 37 74 22 265 81 160 96 128 256), losses := [] }

theorem u7063 : Upper (D 7) (R 7) [36,72,18,257,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7064 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,6),(1,0),(3,6),(4,1)], upper := (rows 37 74 22 265 81 160 192 162 290), lower := (rows 37 74 22 265 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 224 224 128 256), good := (rows 117 104 20 281 113 224 224 224 256) }] }

theorem u7064 : Upper (D 7) (R 7) [36,72,18,257,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7065 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 22 265 145 96 66 160 416), lower := (rows 37 74 22 265 145 96 66 128 256), losses := [] }

theorem u7065 : Upper (D 7) (R 7) [36,72,18,257,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7066 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 3, region := 98, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(1,7)], upper := (rows 37 74 22 265 145 96 96 130 386), lower := (rows 37 74 22 265 145 96 96 128 256), losses := [] }

theorem u7066 : Upper (D 7) (R 7) [36,72,18,257,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7067 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(3,7)], upper := (rows 37 74 22 265 145 96 192 162 290), lower := (rows 37 74 22 265 145 96 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 246 208 128 256), good := (rows 37 104 117 265 241 96 224 224 256) },{ target := 7, region := (rows 5 2 4 13 16 98 64 0 262), good := (rows 301 362 319 265 25 96 96 0 256) }] }

theorem u7067 : Upper (D 7) (R 7) [36,72,18,257,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7068 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 22 296 81 160 65 130 386), lower := (rows 37 74 22 296 81 160 65 128 256), losses := [] }

theorem u7068 : Upper (D 7) (R 7) [36,72,18,288,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7069 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 22 296 81 160 66 129 385), lower := (rows 37 74 22 296 81 160 66 128 256), losses := [] }

theorem u7069 : Upper (D 7) (R 7) [36,72,18,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7070 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(1,0),(3,6),(4,1)], upper := (rows 37 74 22 296 81 160 192 131 259), lower := (rows 37 74 22 296 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 224 224 128 256), good := (rows 100 106 22 362 112 224 224 224 256) },{ target := 1, region := (rows 1 0 4 8 17 224 224 128 256), good := (rows 117 104 20 360 113 224 224 224 256) }] }

theorem u7070 : Upper (D 7) (R 7) [36,72,18,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7071 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 5, region := 394, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 37 74 22 296 145 96 65 130 386), lower := (rows 37 74 22 296 145 96 65 128 256), losses := [] }

theorem u7071 : Upper (D 7) (R 7) [36,72,18,288,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7072 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 22 296 145 96 66 129 385), lower := (rows 37 74 22 296 145 96 66 128 256), losses := [] }

theorem u7072 : Upper (D 7) (R 7) [36,72,18,288,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7073 : Route 9 := (fun mask => (mask,id))

def c7073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7073 : Upper (D 7) (R 7) [36,72,18,288,129,64,128] 13 := by
  apply FastRouting.sound _ _ [36,72,18,288,129,64,128] 13 (by decide) (choices 1) [1,2] r7073 c7073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u520
  · exact u521

def b7074 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 74 22 392 81 160 65 162 290), lower := (rows 37 74 22 392 81 160 65 128 256), losses := [] }

theorem u7074 : Upper (D 7) (R 7) [36,72,18,384,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7075 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 22 392 81 160 66 161 289), lower := (rows 37 74 22 392 81 160 66 128 256), losses := [] }

theorem u7075 : Upper (D 7) (R 7) [36,72,18,384,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7076 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 74 22 392 81 160 96 131 259), lower := (rows 37 74 22 392 81 160 96 128 256), losses := [] }

theorem u7076 : Upper (D 7) (R 7) [36,72,18,384,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7077 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 394, targets := 1 },{ cop := 2, region := 97, targets := 2 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 37 74 22 392 145 96 65 162 290), lower := (rows 37 74 22 392 145 96 65 128 256), losses := [] }

theorem u7077 : Upper (D 7) (R 7) [36,72,18,384,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7078 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 22 392 145 96 66 161 289), lower := (rows 37 74 22 392 145 96 66 128 256), losses := [] }

theorem u7078 : Upper (D 7) (R 7) [36,72,18,384,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7079 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 98, targets := 129 },{ cop := 2, region := 97, targets := 2 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(1,7)], upper := (rows 37 74 22 392 145 96 96 131 259), lower := (rows 37 74 22 392 145 96 96 128 256), losses := [] }

theorem u7079 : Upper (D 7) (R 7) [36,72,18,384,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7079
end Delivery.IrregularNine14.P07
