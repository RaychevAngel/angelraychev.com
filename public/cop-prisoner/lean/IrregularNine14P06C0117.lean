import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0008

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7020 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 300, targets := 2 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 35 134 44 265 81 96 66 148 276), lower := (rows 35 134 44 265 81 96 66 128 256), losses := [] }

theorem u7020 : Upper (D 6) (R 6) [34,132,40,257,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7021 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 116, targets := 2 },{ cop := 3, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 134 44 265 81 96 68 146 274), lower := (rows 35 134 44 265 81 96 68 128 256), losses := [] }

theorem u7021 : Upper (D 6) (R 6) [34,132,40,257,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7022 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 44 265 81 96 80 134 262), lower := (rows 35 134 44 265 81 96 80 128 256), losses := [] }

theorem u7022 : Upper (D 6) (R 6) [34,132,40,257,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7022 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7023 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 44 265 82 96 65 148 276), lower := (rows 35 134 44 265 82 96 65 128 256), losses := [] }

theorem u7023 : Upper (D 6) (R 6) [34,132,40,257,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7024 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 134 44 265 82 96 68 145 273), lower := (rows 35 134 44 265 82 96 68 128 256), losses := [] }

theorem u7024 : Upper (D 6) (R 6) [34,132,40,257,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7025 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 44 265 82 96 80 133 261), lower := (rows 35 134 44 265 82 96 80 128 256), losses := [] }

theorem u7025 : Upper (D 6) (R 6) [34,132,40,257,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7025 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7026 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 116, targets := 2 },{ cop := 4, region := 130, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 134 44 265 84 96 65 146 274), lower := (rows 35 134 44 265 84 96 65 128 256), losses := [] }

theorem u7026 : Upper (D 6) (R 6) [34,132,40,257,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7027 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 97, targets := 4 },{ cop := 1, region := 80, targets := 32 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 35 134 44 265 84 96 66 145 273), lower := (rows 35 134 44 265 84 96 66 128 256), losses := [] }

theorem u7027 : Upper (D 6) (R 6) [34,132,40,257,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7028 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 134 44 265 84 96 80 131 259), lower := (rows 35 134 44 265 84 96 80 128 256), losses := [] }

theorem u7028 : Upper (D 6) (R 6) [34,132,40,257,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7028 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7029 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(3,5)], upper := (rows 35 134 44 266 21 96 65 208 336), lower := (rows 35 134 44 266 21 96 65 128 256), losses := [] }

theorem u7029 : Upper (D 6) (R 6) [34,132,40,258,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7030 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 134 44 266 21 96 80 193 321), lower := (rows 35 134 44 266 21 96 80 128 256), losses := [] }

theorem u7030 : Upper (D 6) (R 6) [34,132,40,258,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7030 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7031 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 134 44 266 81 48 65 196 324), lower := (rows 35 134 44 266 81 48 65 128 256), losses := [] }

theorem u7031 : Upper (D 6) (R 6) [34,132,40,258,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7031 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7032 : PairBound 9 := { available := 65, camps := [], pairs := [(3,5),(4,1)], upper := (rows 35 134 44 266 81 48 68 193 321), lower := (rows 35 134 44 266 81 48 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 49 70 145 273), good := (rows 497 196 108 328 497 432 68 128 256) },{ target := 5, region := (rows 1 2 4 9 17 0 70 145 273), good := (rows 475 198 76 330 473 400 68 128 256) }] }

theorem u7032 : Upper (D 6) (R 6) [34,132,40,258,65,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7032 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7033 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 134 44 266 81 96 65 148 276), lower := (rows 35 134 44 266 81 96 65 128 256), losses := [] }

theorem u7033 : Upper (D 6) (R 6) [34,132,40,258,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7034 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 134 44 266 81 96 68 145 273), lower := (rows 35 134 44 266 81 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 127 78 145 273), good := (rows 497 228 108 364 497 96 100 128 256) }] }

theorem u7034 : Upper (D 6) (R 6) [34,132,40,258,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7035 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 44 266 81 96 80 133 261), lower := (rows 35 134 44 266 81 96 80 128 256), losses := [] }

theorem u7035 : Upper (D 6) (R 6) [34,132,40,258,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7035 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7036 : Route 9 := (fun mask => (mask,id))

def c7036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7036 : Upper (D 6) (R 6) [34,132,40,258,68,64,1] 13 := by
  apply FastRouting.sound _ _ [34,132,40,258,68,64,1] 13 (by decide) (choices 1) [1,16] r7036 c7036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u529
  · exact u530

def b7037 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 134 44 266 84 96 80 129 257), lower := (rows 35 134 44 266 84 96 80 128 256), losses := [] }

theorem u7037 : Upper (D 6) (R 6) [34,132,40,258,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7037 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7038 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 44 280 84 33 65 194 322), lower := (rows 35 134 44 280 84 33 65 128 256), losses := [] }

theorem u7038 : Upper (D 6) (R 6) [34,132,40,272,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7039 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 35 134 44 280 84 33 66 193 321), lower := (rows 35 134 44 280 84 33 66 128 256), losses := [] }

theorem u7039 : Upper (D 6) (R 6) [34,132,40,272,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7040 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 300, targets := 2 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 35 134 44 328 81 33 66 148 276), lower := (rows 35 134 44 328 81 33 66 128 256), losses := [] }

theorem u7040 : Upper (D 6) (R 6) [34,132,40,320,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7041 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 134 44 328 81 33 68 146 274), lower := (rows 35 134 44 328 81 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 49 70 128 256), good := (rows 113 196 108 328 113 49 68 128 256) }] }

theorem u7041 : Upper (D 6) (R 6) [34,132,40,320,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7042 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 44 328 81 33 80 134 262), lower := (rows 35 134 44 328 81 33 80 128 256), losses := [] }

theorem u7042 : Upper (D 6) (R 6) [34,132,40,320,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7042 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7043 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 44 328 82 33 65 148 276), lower := (rows 35 134 44 328 82 33 65 128 256), losses := [] }

theorem u7043 : Upper (D 6) (R 6) [34,132,40,320,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7044 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 35 134 44 328 82 33 68 145 273), lower := (rows 35 134 44 328 82 33 68 128 256), losses := [] }

theorem u7044 : Upper (D 6) (R 6) [34,132,40,320,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7045 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 44 328 82 33 80 133 261), lower := (rows 35 134 44 328 82 33 80 128 256), losses := [] }

theorem u7045 : Upper (D 6) (R 6) [34,132,40,320,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7045 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7046 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 35 134 76 25 276 96 65 162 290), lower := (rows 35 134 76 25 276 96 65 128 256), losses := [] }

theorem u7046 : Upper (D 6) (R 6) [34,132,72,17,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7047 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,5)], upper := (rows 35 134 76 25 276 96 66 161 289), lower := (rows 35 134 76 25 276 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 111 67 128 256), good := (rows 98 230 108 124 308 96 98 128 256) },{ target := 5, region := (rows 1 2 12 8 16 0 67 128 256), good := (rows 67 198 76 93 276 64 66 128 256) }] }

theorem u7047 : Upper (D 6) (R 6) [34,132,72,17,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7048 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 134 76 25 276 96 96 131 259), lower := (rows 35 134 76 25 276 96 96 128 256), losses := [] }

theorem u7048 : Upper (D 6) (R 6) [34,132,72,17,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7049 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 353, targets := 4 }], pairs := [(0,2),(4,1)], upper := (rows 35 134 76 26 52 288 65 193 321), lower := (rows 35 134 76 26 52 288 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 22 357 65 193 321), good := (rows 497 180 508 24 52 288 481 128 288) }] }

theorem u7049 : Upper (D 6) (R 6) [34,132,72,18,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7049 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7050 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 97, targets := 4 },{ cop := 2, region := 162, targets := 1 }], pairs := [(0,2),(1,0),(2,1)], upper := (rows 35 134 76 26 273 96 65 164 292), lower := (rows 35 134 76 26 273 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 125 81 142 270), good := (rows 497 420 492 508 369 96 113 128 256) }] }

theorem u7050 : Upper (D 6) (R 6) [34,132,72,18,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7051 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 76 26 273 96 68 161 289), lower := (rows 35 134 76 26 273 96 68 128 256), losses := [] }

theorem u7051 : Upper (D 6) (R 6) [34,132,72,18,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7052 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 134 76 26 273 96 96 133 261), lower := (rows 35 134 76 26 273 96 96 128 256), losses := [] }

theorem u7052 : Upper (D 6) (R 6) [34,132,72,18,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7053 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 134 76 26 276 33 65 224 352), lower := (rows 35 134 76 26 276 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 22 97 97 229 357), good := (rows 497 404 508 24 404 481 481 128 256) }] }

theorem u7053 : Upper (D 6) (R 6) [34,132,72,18,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7054 : Route 9 := (fun mask => (mask,id))

def c7054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7054 : Upper (D 6) (R 6) [34,132,72,18,260,1,32] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,260,1,32] 13 (by decide) (choices 1) [1,64] r7054 c7054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u531
  · exact u532

def r7055 : Route 9 := (fun mask => (mask,id))

def c7055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7055 : Upper (D 6) (R 6) [34,132,72,18,260,64,1] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,260,64,1] 13 (by decide) (choices 1) [1,32] r7055 c7055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u533
  · exact u534

def b7056 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 134 76 26 276 96 96 129 257), lower := (rows 35 134 76 26 276 96 96 128 256), losses := [] }

theorem u7056 : Upper (D 6) (R 6) [34,132,72,18,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7057 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 130, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 134 76 26 304 33 65 196 324), lower := (rows 35 134 76 26 304 33 65 128 256), losses := [] }

theorem u7057 : Upper (D 6) (R 6) [34,132,72,18,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7058 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 134 76 26 304 33 68 193 321), lower := (rows 35 134 76 26 304 33 68 128 256), losses := [] }

theorem u7058 : Upper (D 6) (R 6) [34,132,72,18,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7059 : Route 9 := (fun mask => (mask,id))

def c7059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7059 : Upper (D 6) (R 6) [34,132,72,18,288,64,1] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,288,64,1] 13 (by decide) (choices 1) [1,4] r7059 c7059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u535
  · exact u536

def b7060 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 76 26 304 96 68 129 257), lower := (rows 35 134 76 26 304 96 68 128 256), losses := [] }

theorem u7060 : Upper (D 6) (R 6) [34,132,72,18,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7061 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 96 },{ cop := 4, region := 108, targets := 2 }], pairs := [(1,5),(1,6),(2,1)], upper := (rows 35 134 76 56 273 96 65 134 262), lower := (rows 35 134 76 56 273 96 65 128 256), losses := [] }

theorem u7061 : Upper (D 6) (R 6) [34,132,72,48,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7062 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(3,0)], upper := (rows 35 134 76 56 273 96 66 133 261), lower := (rows 35 134 76 56 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 119 67 128 256), good := (rows 98 230 108 60 380 96 98 128 256) }] }

theorem u7062 : Upper (D 6) (R 6) [34,132,72,48,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7063 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 76 56 273 96 68 131 259), lower := (rows 35 134 76 56 273 96 68 128 256), losses := [] }

theorem u7063 : Upper (D 6) (R 6) [34,132,72,48,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7064 : Route 9 := (fun mask => (mask,id))

def c7064 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7064 : Upper (D 6) (R 6) [34,132,72,48,258,64,1] 13 := by
  apply FastRouting.sound _ _ [34,132,72,48,258,64,1] 13 (by decide) (choices 1) [1,4] r7064 c7064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u537
  · exact u538

def b7065 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 76 56 274 96 68 129 257), lower := (rows 35 134 76 56 274 96 68 128 256), losses := [] }

theorem u7065 : Upper (D 6) (R 6) [34,132,72,48,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7066 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 76 56 276 33 65 194 322), lower := (rows 35 134 76 56 276 33 65 128 256), losses := [] }

theorem u7066 : Upper (D 6) (R 6) [34,132,72,48,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7067 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 76 56 276 33 66 193 321), lower := (rows 35 134 76 56 276 33 66 128 256), losses := [{ target := 2, region := (rows 67 2 0 24 16 103 67 231 359), good := (rows 483 483 489 440 440 481 483 128 256) }] }

theorem u7067 : Upper (D 6) (R 6) [34,132,72,48,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7068 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 97, targets := 4 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 134 76 265 21 96 66 176 304), lower := (rows 35 134 76 265 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 18 12 8 16 127 83 144 272), good := (rows 98 230 108 364 502 96 98 128 256) }] }

theorem u7068 : Upper (D 6) (R 6) [34,132,72,257,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7069 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 35 134 76 265 21 96 80 162 290), lower := (rows 35 134 76 265 21 96 80 128 256), losses := [] }

theorem u7069 : Upper (D 6) (R 6) [34,132,72,257,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7069 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7070 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 134 76 265 21 96 96 146 274), lower := (rows 35 134 76 265 21 96 96 128 256), losses := [] }

theorem u7070 : Upper (D 6) (R 6) [34,132,72,257,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7071 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 134 76 265 81 48 66 164 292), lower := (rows 35 134 76 265 81 48 66 128 256), losses := [] }

theorem u7071 : Upper (D 6) (R 6) [34,132,72,257,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7071 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7072 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 35 134 76 265 81 48 68 162 290), lower := (rows 35 134 76 265 81 48 68 128 256), losses := [] }

theorem u7072 : Upper (D 6) (R 6) [34,132,72,257,65,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7072 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7073 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 76 265 81 48 96 134 262), lower := (rows 35 134 76 265 81 48 96 128 256), losses := [] }

theorem u7073 : Upper (D 6) (R 6) [34,132,72,257,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7073 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7074 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 297, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 76 265 82 33 68 176 304), lower := (rows 35 134 76 265 82 33 68 128 256), losses := [] }

theorem u7074 : Upper (D 6) (R 6) [34,132,72,257,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7075 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 76 265 82 33 80 164 292), lower := (rows 35 134 76 265 82 33 80 128 256), losses := [] }

theorem u7075 : Upper (D 6) (R 6) [34,132,72,257,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7075 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7076 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 146, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 76 265 82 33 96 148 276), lower := (rows 35 134 76 265 82 33 96 128 256), losses := [] }

theorem u7076 : Upper (D 6) (R 6) [34,132,72,257,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7077 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(3,0)], upper := (rows 35 134 76 266 21 96 65 176 304), lower := (rows 35 134 76 266 21 96 65 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 100 64 144 272), good := (rows 34 166 108 266 446 96 96 128 256) }] }

theorem u7077 : Upper (D 6) (R 6) [34,132,72,258,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7078 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 35 134 76 266 21 96 80 161 289), lower := (rows 35 134 76 266 21 96 80 128 256), losses := [] }

theorem u7078 : Upper (D 6) (R 6) [34,132,72,258,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7078 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7079 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 134 76 266 21 96 96 145 273), lower := (rows 35 134 76 266 21 96 96 128 256), losses := [] }

theorem u7079 : Upper (D 6) (R 6) [34,132,72,258,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7079
end Delivery.IrregularNine14.P06
