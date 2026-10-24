import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0026
import IrregularNine14P07C0027

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13020 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 200 146 33 368 432 304), lower := (rows 7 42 69 200 146 33 64 128 256), losses := [] }

theorem u13020 : Upper (D 7) (R 7) [6,40,65,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13021 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 42 69 200 146 48 353 417 289), lower := (rows 7 42 69 200 146 48 64 128 256), losses := [] }

theorem u13021 : Upper (D 7) (R 7) [6,40,65,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13021 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13022 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 357, targets := 128 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,7),(2,7),(4,6)], upper := (rows 7 42 69 200 146 288 113 177 305), lower := (rows 7 42 69 200 146 288 64 128 256), losses := [] }

theorem u13022 : Upper (D 7) (R 7) [6,40,65,192,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13022 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13023 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 200 176 33 338 402 274), lower := (rows 7 42 69 200 176 33 64 128 256), losses := [] }

theorem u13023 : Upper (D 7) (R 7) [6,40,65,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13024 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 42 69 200 176 34 337 401 273), lower := (rows 7 42 69 200 176 34 64 128 256), losses := [] }

theorem u13024 : Upper (D 7) (R 7) [6,40,65,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13025 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 42 69 200 176 48 323 387 259), lower := (rows 7 42 69 200 176 48 64 128 256), losses := [] }

theorem u13025 : Upper (D 7) (R 7) [6,40,65,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13025 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13026 : Route 9 := (fun mask => (mask,id))

def c13026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13026 : Upper (D 7) (R 7) [6,40,65,192,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,192,160,256] 13 (by decide) (choices 1) [1,2,16] r13026 c13026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1604
  · exact u1605
  · exact u1606

def b13027 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 200 273 34 240 176 432), lower := (rows 7 42 69 200 273 34 64 128 256), losses := [] }

theorem u13027 : Upper (D 7) (R 7) [6,40,65,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13028 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(3,0),(4,6)], upper := (rows 7 42 69 200 273 48 226 162 418), lower := (rows 7 42 69 200 273 48 64 128 256), losses := [] }

theorem u13028 : Upper (D 7) (R 7) [6,40,65,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13028 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13029 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 200 273 160 114 178 306), lower := (rows 7 42 69 200 273 160 64 128 256), losses := [] }

theorem u13029 : Upper (D 7) (R 7) [6,40,65,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13030 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 200 274 33 240 176 432), lower := (rows 7 42 69 200 274 33 64 128 256), losses := [] }

theorem u13030 : Upper (D 7) (R 7) [6,40,65,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13031 : Route 9 := (fun mask => (mask,id))

def c13031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13031 : Upper (D 7) (R 7) [6,40,65,192,258,16] 13 := by
  apply FastRouting.sound _ _ [6,40,65,192,258,16] 13 (by decide) (choices 1) [1,32,128] r13031 c13031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1607
  · exact u1608
  · exact u1609

def b13032 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 200 274 160 113 177 305), lower := (rows 7 42 69 200 274 160 64 128 256), losses := [] }

theorem u13032 : Upper (D 7) (R 7) [6,40,65,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13033 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 200 304 33 210 146 402), lower := (rows 7 42 69 200 304 33 64 128 256), losses := [] }

theorem u13033 : Upper (D 7) (R 7) [6,40,65,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13034 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 200 304 34 209 145 401), lower := (rows 7 42 69 200 304 34 64 128 256), losses := [] }

theorem u13034 : Upper (D 7) (R 7) [6,40,65,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13035 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 42 69 200 304 48 195 131 387), lower := (rows 7 42 69 200 304 48 64 128 256), losses := [] }

theorem u13035 : Upper (D 7) (R 7) [6,40,65,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13035 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13036 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 200 304 160 83 147 275), lower := (rows 7 42 69 200 304 160 64 128 256), losses := [] }

theorem u13036 : Upper (D 7) (R 7) [6,40,65,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13037 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 200 400 33 114 178 306), lower := (rows 7 42 69 200 400 33 64 128 256), losses := [] }

theorem u13037 : Upper (D 7) (R 7) [6,40,65,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13038 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 200 400 34 113 177 305), lower := (rows 7 42 69 200 400 34 64 128 256), losses := [] }

theorem u13038 : Upper (D 7) (R 7) [6,40,65,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13039 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,7),(2,7),(4,6)], upper := (rows 7 42 69 200 400 48 99 163 291), lower := (rows 7 42 69 200 400 48 64 128 256), losses := [] }

theorem u13039 : Upper (D 7) (R 7) [6,40,65,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13039 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13040 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 69 265 112 34 208 144 400), lower := (rows 7 42 69 265 112 34 64 128 256), losses := [] }

theorem u13040 : Upper (D 7) (R 7) [6,40,65,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13041 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 69 265 112 48 194 130 386), lower := (rows 7 42 69 265 112 48 64 128 256), losses := [] }

theorem u13041 : Upper (D 7) (R 7) [6,40,65,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13041 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13042 : Route 9 := (fun mask => (mask,id))

def c13042 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13042 : Upper (D 7) (R 7) [6,40,65,257,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,257,96,128] 13 (by decide) (choices 1) [2,16,128] r13042 c13042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1610
  · exact u1611
  · exact u1612

def b13043 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 42 69 265 146 48 224 224 480), lower := (rows 7 42 69 265 146 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 9 16 48 114 178 306), good := (rows 461 488 77 269 496 496 64 128 256) }] }

theorem u13043 : Upper (D 7) (R 7) [6,40,65,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13043 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13044 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 1, region := 144, targets := 64 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 7 42 69 265 146 96 240 176 432), lower := (rows 7 42 69 265 146 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 19 32 0 130 258), good := (rows 415 442 29 281 402 32 0 128 256) }] }

theorem u13044 : Upper (D 7) (R 7) [6,40,65,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13045 : Route 9 := (fun mask => (mask,id))

def c13045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13045 : Upper (D 7) (R 7) [6,40,65,257,130,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,257,130,128] 13 (by decide) (choices 1) [16,32] r13045 c13045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1613
  · exact u1614

def b13046 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 69 265 176 34 208 208 464), lower := (rows 7 42 69 265 176 34 64 128 256), losses := [] }

theorem u13046 : Upper (D 7) (R 7) [6,40,65,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13047 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 69 265 176 48 194 194 450), lower := (rows 7 42 69 265 176 48 64 128 256), losses := [] }

theorem u13047 : Upper (D 7) (R 7) [6,40,65,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13047 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13048 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 1, region := 144, targets := 64 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 7 42 69 265 176 96 210 146 402), lower := (rows 7 42 69 265 176 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 13 18 32 0 131 259), good := (rows 415 442 397 393 176 32 0 128 256) }] }

theorem u13048 : Upper (D 7) (R 7) [6,40,65,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13049 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 265 176 160 82 210 338), lower := (rows 7 42 69 265 176 160 64 128 256), losses := [] }

theorem u13049 : Upper (D 7) (R 7) [6,40,65,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13050 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 69 265 208 34 240 176 432), lower := (rows 7 42 69 265 208 34 64 128 256), losses := [] }

theorem u13050 : Upper (D 7) (R 7) [6,40,65,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13051 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0),(3,6),(4,0)], upper := (rows 7 42 69 265 208 48 226 162 418), lower := (rows 7 42 69 265 208 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 16 48 0 130 258), good := (rows 399 426 13 265 176 48 0 128 256) }] }

theorem u13051 : Upper (D 7) (R 7) [6,40,65,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13051 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13052 : Route 9 := (fun mask => (mask,id))

def c13052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13052 : Upper (D 7) (R 7) [6,40,65,257,192,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,257,192,128] 13 (by decide) (choices 1) [2,16,32] r13052 c13052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1615
  · exact u1616
  · exact u1617

def b13053 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 69 266 112 33 208 144 400), lower := (rows 7 42 69 266 112 33 64 128 256), losses := [] }

theorem u13053 : Upper (D 7) (R 7) [6,40,65,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13054 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 69 266 112 48 193 129 385), lower := (rows 7 42 69 266 112 48 64 128 256), losses := [] }

theorem u13054 : Upper (D 7) (R 7) [6,40,65,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13054 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13055 : Route 9 := (fun mask => (mask,id))

def c13055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13055 : Upper (D 7) (R 7) [6,40,65,258,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,258,96,128] 13 (by decide) (choices 1) [1,16,128] r13055 c13055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1618
  · exact u1619
  · exact u1620

def b13056 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 69 266 176 33 208 208 464), lower := (rows 7 42 69 266 176 33 64 128 256), losses := [] }

theorem u13056 : Upper (D 7) (R 7) [6,40,65,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13057 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 69 266 176 48 193 193 449), lower := (rows 7 42 69 266 176 48 64 128 256), losses := [] }

theorem u13057 : Upper (D 7) (R 7) [6,40,65,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13057 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13058 : Route 9 := (fun mask => (mask,id))

def c13058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13058 : Upper (D 7) (R 7) [6,40,65,258,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,258,160,64] 13 (by decide) (choices 1) [1,16,128] r13058 c13058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1621
  · exact u1622
  · exact u1623

def b13059 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 266 176 160 81 209 337), lower := (rows 7 42 69 266 176 160 64 128 256), losses := [] }

theorem u13059 : Upper (D 7) (R 7) [6,40,65,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13060 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 69 266 208 33 240 176 432), lower := (rows 7 42 69 266 208 33 64 128 256), losses := [] }

theorem u13060 : Upper (D 7) (R 7) [6,40,65,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13061 : Route 9 := (fun mask => (mask,id))

def c13061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13061 : Upper (D 7) (R 7) [6,40,65,258,192,16] 13 := by
  apply FastRouting.sound _ _ [6,40,65,258,192,16] 13 (by decide) (choices 1) [1,32,128] r13061 c13061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1624
  · exact u1625
  · exact u1626

def r13062 : Route 9 := (fun mask => (mask,id))

def c13062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13062 : Upper (D 7) (R 7) [6,40,65,258,192,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,258,192,128] 13 (by decide) (choices 1) [1,16,32] r13062 c13062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1627
  · exact u1628
  · exact u1629

def b13063 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 42 69 280 112 33 194 130 386), lower := (rows 7 42 69 280 112 33 64 128 256), losses := [] }

theorem u13063 : Upper (D 7) (R 7) [6,40,65,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13064 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 69 280 112 34 193 129 385), lower := (rows 7 42 69 280 112 34 64 128 256), losses := [] }

theorem u13064 : Upper (D 7) (R 7) [6,40,65,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13065 : Route 9 := (fun mask => (mask,id))

def c13065 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13065 : Upper (D 7) (R 7) [6,40,65,272,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,96,128] 13 (by decide) (choices 1) [1,2,128] r13065 c13065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1630
  · exact u1631
  · exact u1632

def b13066 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 34, targets := 192 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 69 280 145 34 224 224 480), lower := (rows 7 42 69 280 145 34 64 128 256), losses := [] }

theorem u13066 : Upper (D 7) (R 7) [6,40,65,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13067 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(3,6),(4,6)], upper := (rows 7 42 69 280 145 96 226 162 418), lower := (rows 7 42 69 280 145 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 17 32 0 130 258), good := (rows 415 426 29 280 153 32 0 128 256) }] }

theorem u13067 : Upper (D 7) (R 7) [6,40,65,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13068 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 7 42 69 280 145 160 98 226 354), lower := (rows 7 42 69 280 145 160 64 128 256), losses := [] }

theorem u13068 : Upper (D 7) (R 7) [6,40,65,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13069 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 69 280 146 33 224 224 480), lower := (rows 7 42 69 280 146 33 64 128 256), losses := [] }

theorem u13069 : Upper (D 7) (R 7) [6,40,65,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13070 : Route 9 := (fun mask => (mask,id))

def c13070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13070 : Upper (D 7) (R 7) [6,40,65,272,130,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,130,64] 13 (by decide) (choices 1) [1,32,128] r13070 c13070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1633
  · exact u1634
  · exact u1635

def b13071 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,7),(1,0),(2,1),(2,7)], upper := (rows 7 42 69 280 146 160 97 225 353), lower := (rows 7 42 69 280 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 6 42 68 314 178 160 64 160 256) }] }

theorem u13071 : Upper (D 7) (R 7) [6,40,65,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13072 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 42 69 280 176 33 194 194 450), lower := (rows 7 42 69 280 176 33 64 128 256), losses := [] }

theorem u13072 : Upper (D 7) (R 7) [6,40,65,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13073 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 69 280 176 34 193 193 449), lower := (rows 7 42 69 280 176 34 64 128 256), losses := [] }

theorem u13073 : Upper (D 7) (R 7) [6,40,65,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13074 : Route 9 := (fun mask => (mask,id))

def c13074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13074 : Upper (D 7) (R 7) [6,40,65,272,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,160,64] 13 (by decide) (choices 1) [1,2,128] r13074 c13074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1636
  · exact u1637
  · exact u1638

def b13075 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 280 176 160 67 195 323), lower := (rows 7 42 69 280 176 160 64 128 256), losses := [] }

theorem u13075 : Upper (D 7) (R 7) [6,40,65,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13076 : Route 9 := (fun mask => (mask,id))

def c13076 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13076 : Upper (D 7) (R 7) [6,40,65,272,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,192,1] 13 (by decide) (choices 1) [2,32,128] r13076 c13076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1639
  · exact u1640
  · exact u1641

def r13077 : Route 9 := (fun mask => (mask,id))

def c13077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13077 : Upper (D 7) (R 7) [6,40,65,272,192,2] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,192,2] 13 (by decide) (choices 1) [1,32,128] r13077 c13077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1642
  · exact u1643
  · exact u1644

def b13078 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 7 42 69 280 208 160 99 163 291), lower := (rows 7 42 69 280 208 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 6 42 68 314 240 160 64 160 256) },{ target := 6, region := (rows 1 10 4 8 16 181 0 129 257), good := (rows 423 42 421 314 176 160 0 160 256) }] }

theorem u13078 : Upper (D 7) (R 7) [6,40,65,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13079 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 69 328 49 34 208 144 400), lower := (rows 7 42 69 328 49 34 64 128 256), losses := [] }

theorem u13079 : Upper (D 7) (R 7) [6,40,65,320,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13079
end Delivery.IrregularNine14.P07
