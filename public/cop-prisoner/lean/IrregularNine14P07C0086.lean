import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5160 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 1, region := 440, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 296 208 160 65 146 274), lower := (rows 35 70 13 296 208 160 65 128 256), losses := [] }

theorem u5160 : Upper (D 7) (R 7) [34,68,9,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5161 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 2, region := 66, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 35 70 13 296 208 160 66 145 273), lower := (rows 35 70 13 296 208 160 66 128 256), losses := [] }

theorem u5161 : Upper (D 7) (R 7) [34,68,9,288,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5162 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 13 296 208 160 80 131 259), lower := (rows 35 70 13 296 208 160 80 128 256), losses := [] }

theorem u5162 : Upper (D 7) (R 7) [34,68,9,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5162 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5163 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 144, targets := 2 }], pairs := [(1,0),(1,5),(1,7),(4,1)], upper := (rows 35 70 13 328 145 160 66 176 304), lower := (rows 35 70 13 328 145 160 66 128 256), losses := [] }

theorem u5163 : Upper (D 7) (R 7) [34,68,9,320,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5164 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 1, region := 424, targets := 1 }], pairs := [(0,6),(3,0),(4,6)], upper := (rows 35 70 13 328 145 160 80 162 290), lower := (rows 35 70 13 328 145 160 80 128 256), losses := [] }

theorem u5164 : Upper (D 7) (R 7) [34,68,9,320,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5164 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5165 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,6),(1,0),(4,5),(4,6)], upper := (rows 35 70 13 328 145 160 96 146 274), lower := (rows 35 70 13 328 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 176 241 128 256), good := (rows 98 70 78 328 240 224 96 224 256) }] }

theorem u5165 : Upper (D 7) (R 7) [34,68,9,320,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5166 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(4,0),(4,6)], upper := (rows 35 70 13 328 146 160 65 176 304), lower := (rows 35 70 13 328 146 160 65 128 256), losses := [] }

theorem u5166 : Upper (D 7) (R 7) [34,68,9,320,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5167 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 35 70 13 328 146 160 80 161 289), lower := (rows 35 70 13 328 146 160 80 128 256), losses := [{ target := 1, region := (rows 1 0 5 10 16 183 80 133 261), good := (rows 429 492 429 328 248 160 112 160 256) }] }

theorem u5167 : Upper (D 7) (R 7) [34,68,9,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5167 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5168 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,6),(1,0),(4,5),(4,6)], upper := (rows 35 70 13 328 146 160 96 145 273), lower := (rows 35 70 13 328 146 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 176 241 128 256), good := (rows 98 70 78 328 242 224 96 224 256) }] }

theorem u5168 : Upper (D 7) (R 7) [34,68,9,320,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5169 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 82, targets := 160 }], pairs := [(1,5),(1,7),(4,5),(4,7)], upper := (rows 35 70 13 392 81 160 66 176 304), lower := (rows 35 70 13 392 81 160 66 128 256), losses := [] }

theorem u5169 : Upper (D 7) (R 7) [34,68,9,384,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5170 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 82, targets := 160 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 35 70 13 392 81 160 80 162 290), lower := (rows 35 70 13 392 81 160 80 128 256), losses := [] }

theorem u5170 : Upper (D 7) (R 7) [34,68,9,384,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5170 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5171 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 13 392 81 160 96 146 274), lower := (rows 35 70 13 392 81 160 96 128 256), losses := [] }

theorem u5171 : Upper (D 7) (R 7) [34,68,9,384,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5172 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 160 }], pairs := [(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 70 13 392 112 160 65 146 274), lower := (rows 35 70 13 392 112 160 65 128 256), losses := [] }

theorem u5172 : Upper (D 7) (R 7) [34,68,9,384,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5173 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 35 70 13 392 112 160 66 145 273), lower := (rows 35 70 13 392 112 160 66 128 256), losses := [] }

theorem u5173 : Upper (D 7) (R 7) [34,68,9,384,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5174 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 13 392 112 160 80 131 259), lower := (rows 35 70 13 392 112 160 80 128 256), losses := [] }

theorem u5174 : Upper (D 7) (R 7) [34,68,9,384,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5174 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5175 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 35 70 14 25 336 160 65 160 416), lower := (rows 35 70 14 25 336 160 65 128 256), losses := [] }

theorem u5175 : Upper (D 7) (R 7) [34,68,10,17,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5176 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,0),(3,1),(4,1)], upper := (rows 35 70 14 25 336 160 96 129 385), lower := (rows 35 70 14 25 336 160 96 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 160 225 128 256), good := (rows 98 70 14 94 336 224 96 224 256) }] }

theorem u5176 : Upper (D 7) (R 7) [34,68,10,17,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5177 : Route 9 := (fun mask => (mask,id))

def c5177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5177 : Upper (D 7) (R 7) [34,68,10,17,320,128,128] 13 := by
  apply FastRouting.sound _ _ [34,68,10,17,320,128,128] 13 (by decide) (choices 1) [1,32] r5177 c5177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u386
  · exact u387

def b5178 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 70 14 137 112 288 65 144 400), lower := (rows 35 70 14 137 112 288 65 128 256), losses := [] }

theorem u5178 : Upper (D 7) (R 7) [34,68,10,129,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5178 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5179 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 14 137 112 288 80 129 385), lower := (rows 35 70 14 137 112 288 80 128 256), losses := [] }

theorem u5179 : Upper (D 7) (R 7) [34,68,10,129,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5179 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5180 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 14 137 112 288 192 145 273), lower := (rows 35 70 14 137 112 288 192 128 256), losses := [] }

theorem u5180 : Upper (D 7) (R 7) [34,68,10,129,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5180 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5181 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 70 14 137 176 288 65 208 336), lower := (rows 35 70 14 137 176 288 65 128 256), losses := [] }

theorem u5181 : Upper (D 7) (R 7) [34,68,10,129,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5181 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5182 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 35 70 14 137 176 288 80 193 321), lower := (rows 35 70 14 137 176 288 80 128 256), losses := [] }

theorem u5182 : Upper (D 7) (R 7) [34,68,10,129,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5182 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5183 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 14 137 208 288 65 176 304), lower := (rows 35 70 14 137 208 288 65 128 256), losses := [] }

theorem u5183 : Upper (D 7) (R 7) [34,68,10,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5183 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5184 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 86, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 14 137 208 288 80 161 289), lower := (rows 35 70 14 137 208 288 80 128 256), losses := [] }

theorem u5184 : Upper (D 7) (R 7) [34,68,10,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5184 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5185 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 35 70 14 137 208 288 96 145 273), lower := (rows 35 70 14 137 208 288 96 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 24 288 353 128 256), good := (rows 98 70 30 222 208 352 96 128 352) }] }

theorem u5185 : Upper (D 7) (R 7) [34,68,10,129,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5185 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5186 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 86, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 70 14 265 81 160 80 160 416), lower := (rows 35 70 14 265 81 160 80 128 256), losses := [] }

theorem u5186 : Upper (D 7) (R 7) [34,68,10,257,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5186 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5187 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 472, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(3,5)], upper := (rows 35 70 14 265 81 160 96 144 400), lower := (rows 35 70 14 265 81 160 96 128 256), losses := [] }

theorem u5187 : Upper (D 7) (R 7) [34,68,10,257,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5188 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 4, region := 424, targets := 64 }], pairs := [(3,1),(3,6),(4,1),(4,5)], upper := (rows 35 70 14 265 81 160 192 176 304), lower := (rows 35 70 14 265 81 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 224 128 256), good := (rows 83 70 14 281 81 192 192 192 256) }] }

theorem u5188 : Upper (D 7) (R 7) [34,68,10,257,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5189 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 35 70 14 265 112 160 65 144 400), lower := (rows 35 70 14 265 112 160 65 128 256), losses := [] }

theorem u5189 : Upper (D 7) (R 7) [34,68,10,257,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5190 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 14 265 112 160 80 129 385), lower := (rows 35 70 14 265 112 160 80 128 256), losses := [] }

theorem u5190 : Upper (D 7) (R 7) [34,68,10,257,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5190 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5191 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 14 265 112 160 192 145 273), lower := (rows 35 70 14 265 112 160 192 128 256), losses := [] }

theorem u5191 : Upper (D 7) (R 7) [34,68,10,257,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5192 : Route 9 := (fun mask => (mask,id))

def c5192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5192 : Upper (D 7) (R 7) [34,68,10,257,129,128,16] 13 := by
  apply FastRouting.sound _ _ [34,68,10,257,129,128,16] 13 (by decide) (choices 1) [32,64] r5192 c5192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u388
  · exact u389

def b5193 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 35 70 14 265 145 160 96 208 336), lower := (rows 35 70 14 265 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 176 241 144 272), good := (rows 98 70 14 334 496 224 96 224 256) }] }

theorem u5193 : Upper (D 7) (R 7) [34,68,10,257,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5194 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 35 70 14 265 208 160 65 176 304), lower := (rows 35 70 14 265 208 160 65 128 256), losses := [] }

theorem u5194 : Upper (D 7) (R 7) [34,68,10,257,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5195 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 14 265 208 160 80 161 289), lower := (rows 35 70 14 265 208 160 80 128 256), losses := [] }

theorem u5195 : Upper (D 7) (R 7) [34,68,10,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5195 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5196 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 5, region := 80, targets := 1 }], pairs := [(1,0),(3,1),(4,0),(4,1)], upper := (rows 35 70 14 265 208 160 96 145 273), lower := (rows 35 70 14 265 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 176 176 241 128 256), good := (rows 114 70 14 334 240 240 112 240 256) }] }

theorem u5196 : Upper (D 7) (R 7) [34,68,10,257,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5197 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 80, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 70 14 280 112 160 65 129 385), lower := (rows 35 70 14 280 112 160 65 128 256), losses := [] }

theorem u5197 : Upper (D 7) (R 7) [34,68,10,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5198 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 14 280 112 160 192 129 257), lower := (rows 35 70 14 280 112 160 192 128 256), losses := [] }

theorem u5198 : Upper (D 7) (R 7) [34,68,10,272,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5199 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 35 70 14 280 208 160 65 161 289), lower := (rows 35 70 14 280 208 160 65 128 256), losses := [{ target := 6, region := (rows 7 2 4 24 16 247 0 199 327), good := (rows 419 423 431 312 440 160 417 160 256) }] }

theorem u5199 : Upper (D 7) (R 7) [34,68,10,272,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5200 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 161, targets := 64 },{ cop := 5, region := 80, targets := 1 }], pairs := [(0,6),(3,1),(4,0),(4,1)], upper := (rows 35 70 14 280 208 160 96 129 257), lower := (rows 35 70 14 280 208 160 96 128 256), losses := [] }

theorem u5200 : Upper (D 7) (R 7) [34,68,10,272,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5201 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 0, region := 472, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 35 70 14 296 145 160 65 208 336), lower := (rows 35 70 14 296 145 160 65 128 256), losses := [] }

theorem u5201 : Upper (D 7) (R 7) [34,68,10,288,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5202 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 35 70 14 296 145 160 80 193 321), lower := (rows 35 70 14 296 145 160 80 128 256), losses := [] }

theorem u5202 : Upper (D 7) (R 7) [34,68,10,288,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5202 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5203 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 0, region := 472, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 35 70 14 296 208 160 65 145 273), lower := (rows 35 70 14 296 208 160 65 128 256), losses := [] }

theorem u5203 : Upper (D 7) (R 7) [34,68,10,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5204 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 14 296 208 160 80 129 257), lower := (rows 35 70 14 296 208 160 80 128 256), losses := [] }

theorem u5204 : Upper (D 7) (R 7) [34,68,10,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5204 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5205 : Route 9 := (fun mask => (mask,id))

def c5205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5205 : Upper (D 7) (R 7) [34,68,10,384,129,16,1] 13 := by
  apply FastRouting.sound _ _ [34,68,10,384,129,16,1] 13 (by decide) (choices 1) [32,64] r5205 c5205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u390
  · exact u391

def r5206 : Route 9 := (fun mask => (mask,id))

def c5206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5206 : Upper (D 7) (R 7) [34,68,10,384,129,16,32] 13 := by
  apply FastRouting.sound _ _ [34,68,10,384,129,16,32] 13 (by decide) (choices 1) [1,64] r5206 c5206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u392
  · exact u393

def b5207 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,1),(3,7),(4,6)], upper := (rows 35 70 28 104 273 160 65 130 386), lower := (rows 35 70 28 104 273 160 65 128 256), losses := [] }

theorem u5207 : Upper (D 7) (R 7) [34,68,24,96,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5208 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 400, targets := 2 }], pairs := [(1,0),(1,5),(1,7),(4,1)], upper := (rows 35 70 28 104 273 160 66 129 385), lower := (rows 35 70 28 104 273 160 66 128 256), losses := [] }

theorem u5208 : Upper (D 7) (R 7) [34,68,24,96,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5209 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 28 104 273 160 192 131 259), lower := (rows 35 70 28 104 273 160 192 128 256), losses := [] }

theorem u5209 : Upper (D 7) (R 7) [34,68,24,96,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5210 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 336, targets := 2 },{ cop := 0, region := 336, targets := 128 },{ cop := 1, region := 168, targets := 1 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(3,0),(4,1),(4,7)], upper := (rows 35 70 28 138 273 160 65 224 352), lower := (rows 35 70 28 138 273 160 65 128 256), losses := [] }

theorem u5210 : Upper (D 7) (R 7) [34,68,24,130,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5211 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 2 },{ cop := 0, region := 336, targets := 128 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(4,1),(4,7)], upper := (rows 35 70 28 138 273 160 96 193 321), lower := (rows 35 70 28 138 273 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 237 128 256), good := (rows 98 70 126 234 336 224 96 224 256) }] }

theorem u5211 : Upper (D 7) (R 7) [34,68,24,130,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5212 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 272, targets := 128 },{ cop := 1, region := 168, targets := 1 }], pairs := [(0,6),(3,0),(4,6),(4,7)], upper := (rows 35 70 28 200 273 160 65 162 290), lower := (rows 35 70 28 200 273 160 65 128 256), losses := [] }

theorem u5212 : Upper (D 7) (R 7) [34,68,24,192,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5213 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 272, targets := 2 }], pairs := [(1,0),(1,5),(1,7),(4,1)], upper := (rows 35 70 28 200 273 160 66 161 289), lower := (rows 35 70 28 200 273 160 66 128 256), losses := [] }

theorem u5213 : Upper (D 7) (R 7) [34,68,24,192,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5214 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(0,6),(3,0),(3,1),(4,6)], upper := (rows 35 70 28 200 273 160 96 131 259), lower := (rows 35 70 28 200 273 160 96 128 256), losses := [] }

theorem u5214 : Upper (D 7) (R 7) [34,68,24,192,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5215 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 44 137 208 288 65 146 274), lower := (rows 35 70 44 137 208 288 65 128 256), losses := [] }

theorem u5215 : Upper (D 7) (R 7) [34,68,40,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5215 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5216 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 35 70 44 137 208 288 66 145 273), lower := (rows 35 70 44 137 208 288 66 128 256), losses := [] }

theorem u5216 : Upper (D 7) (R 7) [34,68,40,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5216 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5217 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 44 137 208 288 80 131 259), lower := (rows 35 70 44 137 208 288 80 128 256), losses := [] }

theorem u5217 : Upper (D 7) (R 7) [34,68,40,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5217 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5218 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 35 70 44 265 81 160 66 144 400), lower := (rows 35 70 44 265 81 160 66 128 256), losses := [] }

theorem u5218 : Upper (D 7) (R 7) [34,68,40,257,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5219 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 44 265 81 160 80 130 386), lower := (rows 35 70 44 265 81 160 80 128 256), losses := [] }

theorem u5219 : Upper (D 7) (R 7) [34,68,40,257,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5219 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5219
end Delivery.IrregularNine14.P07
