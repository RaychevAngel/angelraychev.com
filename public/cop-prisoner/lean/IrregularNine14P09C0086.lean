import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0031

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5160 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,8),(1,5),(2,8),(3,8),(4,8)], upper := (rows 35 194 44 88 148 33 321 385 257), lower := (rows 35 194 44 88 148 33 64 128 256), losses := [] }

theorem u5160 : Upper (D 9) (R 9) [34,192,40,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5160 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5161 : Route 9 := (fun mask => (mask,id))

def c5161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5161 : Upper (D 9) (R 9) [34,192,40,80,132,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,132,256] 13 (by decide) (choices 1) [1,256] r5161 c5161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1874
  · exact u1875

def b5162 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,6),(0,7),(0,8),(1,0),(1,5)], upper := (rows 35 194 44 88 273 33 452 388 388), lower := (rows 35 194 44 88 273 33 64 128 256), losses := [] }

theorem u5162 : Upper (D 9) (R 9) [34,192,40,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5162 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5163 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 36, targets := 449 }], pairs := [(2,0),(2,6),(2,7),(2,8)], upper := (rows 35 194 44 88 273 36 449 385 385), lower := (rows 35 194 44 88 273 36 64 128 256), losses := [] }

theorem u5163 : Upper (D 9) (R 9) [34,192,40,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5163 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5164 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 88 273 160 325 389 261), lower := (rows 35 194 44 88 273 160 64 128 256), losses := [] }

theorem u5164 : Upper (D 9) (R 9) [34,192,40,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5164 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5165 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8),(1,8),(2,0),(2,6),(2,7)], upper := (rows 35 194 44 88 273 288 197 133 389), lower := (rows 35 194 44 88 273 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 304 64 128 256), good := (rows 34 194 44 124 304 288 64 128 288) },{ target := 6, region := (rows 1 2 12 8 16 304 0 128 256), good := (rows 35 130 44 60 305 288 0 128 288) },{ target := 7, region := (rows 1 2 12 8 16 304 64 0 256), good := (rows 35 66 44 124 305 288 64 0 288) }] }

theorem u5165 : Upper (D 9) (R 9) [34,192,40,80,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5165 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5166 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,5),(3,5)], upper := (rows 35 194 44 88 276 33 449 385 385), lower := (rows 35 194 44 88 276 33 64 128 256), losses := [{ target := 5, region := (rows 1 39 4 12 20 0 97 161 289), good := (rows 451 194 478 88 286 451 64 128 256) }] }

theorem u5166 : Upper (D 9) (R 9) [34,192,40,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5166 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5167 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 88 276 160 321 385 257), lower := (rows 35 194 44 88 276 160 64 128 256), losses := [] }

theorem u5167 : Upper (D 9) (R 9) [34,192,40,80,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5167 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5168 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 195, targets := 256 },{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,8),(1,5),(1,8),(2,0)], upper := (rows 35 194 44 88 276 288 193 129 385), lower := (rows 35 194 44 88 276 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 304 64 128 256), good := (rows 34 194 44 124 308 288 64 128 288) }] }

theorem u5168 : Upper (D 9) (R 9) [34,192,40,80,260,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5168 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5169 : Route 9 := (fun mask => (mask,id))

def c5169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5169 : Upper (D 9) (R 9) [34,192,40,80,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,384,1] 13 (by decide) (choices 1) [1,4,256] r5169 c5169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1876
  · exact u1877
  · exact u1878

def b5170 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 36, targets := 449 }], pairs := [(2,0),(2,6),(2,7),(2,8)], upper := (rows 35 194 44 88 400 36 321 385 257), lower := (rows 35 194 44 88 400 36 64 128 256), losses := [] }

theorem u5170 : Upper (D 9) (R 9) [34,192,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5170 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5171 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8),(1,8),(2,0),(2,6),(2,7)], upper := (rows 35 194 44 88 400 288 69 133 261), lower := (rows 35 194 44 88 400 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 304 64 128 256), good := (rows 34 194 44 124 432 288 64 128 288) },{ target := 6, region := (rows 1 2 12 8 16 304 0 128 256), good := (rows 35 130 44 60 432 288 0 128 288) },{ target := 7, region := (rows 1 2 12 8 16 304 64 0 256), good := (rows 35 66 44 124 304 288 64 0 288) }] }

theorem u5171 : Upper (D 9) (R 9) [34,192,40,80,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5171 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5172 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 36, targets := 449 }], pairs := [(2,0),(2,6),(2,7),(2,8)], upper := (rows 35 194 44 265 81 36 464 400 400), lower := (rows 35 194 44 265 81 36 64 128 256), losses := [] }

theorem u5172 : Upper (D 9) (R 9) [34,192,40,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5172 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5173 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 49, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 194 44 265 81 48 452 388 388), lower := (rows 35 194 44 265 81 48 64 128 256), losses := [] }

theorem u5173 : Upper (D 9) (R 9) [34,192,40,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5173 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5174 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 49, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(4,7),(4,8)], upper := (rows 35 194 44 265 81 160 340 404 276), lower := (rows 35 194 44 265 81 160 64 128 256), losses := [] }

theorem u5174 : Upper (D 9) (R 9) [34,192,40,257,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5174 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5175 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 35 194 44 265 81 288 212 148 404), lower := (rows 35 194 44 265 81 288 64 128 256), losses := [] }

theorem u5175 : Upper (D 9) (R 9) [34,192,40,257,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5175 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5176 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 44 265 84 33 464 400 400), lower := (rows 35 194 44 265 84 33 64 128 256), losses := [] }

theorem u5176 : Upper (D 9) (R 9) [34,192,40,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5176 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5177 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(3,6)], upper := (rows 35 194 44 265 84 48 449 385 385), lower := (rows 35 194 44 265 84 48 64 128 256), losses := [] }

theorem u5177 : Upper (D 9) (R 9) [34,192,40,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5177 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5178 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 265 84 160 337 401 273), lower := (rows 35 194 44 265 84 160 64 128 256), losses := [] }

theorem u5178 : Upper (D 9) (R 9) [34,192,40,257,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5178 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5179 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 35 194 44 265 84 288 209 145 401), lower := (rows 35 194 44 265 84 288 64 128 256), losses := [] }

theorem u5179 : Upper (D 9) (R 9) [34,192,40,257,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5179 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5180 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 3, region := 36, targets := 64 }], pairs := [(1,0),(1,5),(2,6),(4,0),(4,5)], upper := (rows 35 194 44 265 276 33 208 208 464), lower := (rows 35 194 44 265 276 33 64 128 256), losses := [] }

theorem u5180 : Upper (D 9) (R 9) [34,192,40,257,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5180 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5181 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 52, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(4,0)], upper := (rows 35 194 44 265 276 48 193 193 449), lower := (rows 35 194 44 265 276 48 64 128 256), losses := [] }

theorem u5181 : Upper (D 9) (R 9) [34,192,40,257,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5181 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5182 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 194 44 265 276 96 209 145 401), lower := (rows 35 194 44 265 276 96 64 128 256), losses := [] }

theorem u5182 : Upper (D 9) (R 9) [34,192,40,257,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5182 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5183 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 466, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 44 265 336 33 212 148 404), lower := (rows 35 194 44 265 336 33 64 128 256), losses := [] }

theorem u5183 : Upper (D 9) (R 9) [34,192,40,257,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5183 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5184 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 36, targets := 449 }], pairs := [(2,0),(2,6),(2,7),(2,8)], upper := (rows 35 194 44 265 336 36 209 145 401), lower := (rows 35 194 44 265 336 36 64 128 256), losses := [] }

theorem u5184 : Upper (D 9) (R 9) [34,192,40,257,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5184 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5185 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8),(1,8),(2,6),(3,6)], upper := (rows 35 194 44 265 336 48 197 133 389), lower := (rows 35 194 44 265 336 48 64 128 256), losses := [] }

theorem u5185 : Upper (D 9) (R 9) [34,192,40,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5185 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5186 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 265 336 160 85 149 277), lower := (rows 35 194 44 265 336 160 64 128 256), losses := [] }

theorem u5186 : Upper (D 9) (R 9) [34,192,40,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5186 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5187 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 49, targets := 384 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(0,8),(1,5),(4,7),(4,8)], upper := (rows 35 194 44 268 81 33 464 400 400), lower := (rows 35 194 44 268 81 33 64 128 256), losses := [] }

theorem u5187 : Upper (D 9) (R 9) [34,192,40,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5187 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5188 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 49, targets := 384 }], pairs := [(0,7),(0,8),(4,7),(4,8)], upper := (rows 35 194 44 268 81 48 449 385 385), lower := (rows 35 194 44 268 81 48 64 128 256), losses := [] }

theorem u5188 : Upper (D 9) (R 9) [34,192,40,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5188 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5189 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,5),(4,7)], upper := (rows 35 194 44 268 81 160 337 401 273), lower := (rows 35 194 44 268 81 160 64 128 256), losses := [] }

theorem u5189 : Upper (D 9) (R 9) [34,192,40,260,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5189 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5190 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 12, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(3,0),(3,6)], upper := (rows 35 194 44 268 81 288 209 145 401), lower := (rows 35 194 44 268 81 288 64 128 256), losses := [] }

theorem u5190 : Upper (D 9) (R 9) [34,192,40,260,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5190 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5191 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 44, targets := 192 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 44 268 273 33 208 208 464), lower := (rows 35 194 44 268 273 33 64 128 256), losses := [] }

theorem u5191 : Upper (D 9) (R 9) [34,192,40,260,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5191 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5192 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(3,0)], upper := (rows 35 194 44 268 273 48 193 193 449), lower := (rows 35 194 44 268 273 48 64 128 256), losses := [] }

theorem u5192 : Upper (D 9) (R 9) [34,192,40,260,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5192 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5193 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,5),(4,6)], upper := (rows 35 194 44 268 273 96 209 145 401), lower := (rows 35 194 44 268 273 96 64 128 256), losses := [] }

theorem u5193 : Upper (D 9) (R 9) [34,192,40,260,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5193 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5194 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(1,5),(4,5)], upper := (rows 35 194 44 268 336 33 209 145 401), lower := (rows 35 194 44 268 336 33 64 128 256), losses := [] }

theorem u5194 : Upper (D 9) (R 9) [34,192,40,260,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5194 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5195 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(3,0)], upper := (rows 35 194 44 268 336 48 193 129 385), lower := (rows 35 194 44 268 336 48 64 128 256), losses := [] }

theorem u5195 : Upper (D 9) (R 9) [34,192,40,260,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5195 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5196 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,5),(4,7)], upper := (rows 35 194 44 268 336 160 81 145 273), lower := (rows 35 194 44 268 336 160 64 128 256), losses := [] }

theorem u5196 : Upper (D 9) (R 9) [34,192,40,260,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5196 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5197 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 49, targets := 384 },{ cop := 2, region := 450, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(4,7),(4,8)], upper := (rows 35 194 44 280 81 33 452 388 388), lower := (rows 35 194 44 280 81 33 64 128 256), losses := [] }

theorem u5197 : Upper (D 9) (R 9) [34,192,40,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5197 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5198 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 36, targets := 449 }], pairs := [(2,0),(2,6),(2,7),(2,8)], upper := (rows 35 194 44 280 81 36 449 385 385), lower := (rows 35 194 44 280 81 36 64 128 256), losses := [] }

theorem u5198 : Upper (D 9) (R 9) [34,192,40,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5198 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5199 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 49, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(4,7),(4,8)], upper := (rows 35 194 44 280 81 160 325 389 261), lower := (rows 35 194 44 280 81 160 64 128 256), losses := [] }

theorem u5199 : Upper (D 9) (R 9) [34,192,40,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5199 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5200 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 35 194 44 280 81 288 197 133 389), lower := (rows 35 194 44 280 81 288 64 128 256), losses := [] }

theorem u5200 : Upper (D 9) (R 9) [34,192,40,272,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5200 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5201 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,5),(3,5)], upper := (rows 35 194 44 280 84 33 449 385 385), lower := (rows 35 194 44 280 84 33 64 128 256), losses := [{ target := 5, region := (rows 1 39 4 12 20 0 97 161 289), good := (rows 451 194 478 280 94 451 64 128 256) }] }

theorem u5201 : Upper (D 9) (R 9) [34,192,40,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5201 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5202 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 280 84 160 321 385 257), lower := (rows 35 194 44 280 84 160 64 128 256), losses := [] }

theorem u5202 : Upper (D 9) (R 9) [34,192,40,272,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5202 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5203 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 35 194 44 280 84 288 193 129 385), lower := (rows 35 194 44 280 84 288 64 128 256), losses := [] }

theorem u5203 : Upper (D 9) (R 9) [34,192,40,272,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5203 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5204 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 49, targets := 320 },{ cop := 4, region := 364, targets := 128 }], pairs := [(0,6),(0,8),(2,7),(4,6),(4,8)], upper := (rows 35 194 44 328 145 33 340 404 276), lower := (rows 35 194 44 328 145 33 64 128 256), losses := [] }

theorem u5204 : Upper (D 9) (R 9) [34,192,40,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5204 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5205 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 36, targets := 449 }], pairs := [(2,0),(2,6),(2,7),(2,8)], upper := (rows 35 194 44 328 145 36 337 401 273), lower := (rows 35 194 44 328 145 36 64 128 256), losses := [] }

theorem u5205 : Upper (D 9) (R 9) [34,192,40,320,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5205 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5206 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 49, targets := 320 }], pairs := [(0,6),(0,8),(4,6),(4,8)], upper := (rows 35 194 44 328 145 48 325 389 261), lower := (rows 35 194 44 328 145 48 64 128 256), losses := [] }

theorem u5206 : Upper (D 9) (R 9) [34,192,40,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5206 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5207 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 35 194 44 328 145 288 85 149 277), lower := (rows 35 194 44 328 145 288 64 128 256), losses := [] }

theorem u5207 : Upper (D 9) (R 9) [34,192,40,320,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5207 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5208 : Route 9 := (fun mask => (mask,id))

def c5208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5208 : Upper (D 9) (R 9) [34,192,40,320,132,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,132,1] 13 (by decide) (choices 1) [1,16,256] r5208 c5208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1879
  · exact u1880
  · exact u1881

def b5209 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 332, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(3,7)], upper := (rows 35 194 44 328 148 48 321 385 257), lower := (rows 35 194 44 328 148 48 64 128 256), losses := [] }

theorem u5209 : Upper (D 9) (R 9) [34,192,40,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5209 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5210 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 35 194 44 328 148 288 81 145 273), lower := (rows 35 194 44 328 148 288 64 128 256), losses := [] }

theorem u5210 : Upper (D 9) (R 9) [34,192,40,320,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5210 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5211 : Route 9 := (fun mask => (mask,id))

def c5211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5211 : Upper (D 9) (R 9) [34,192,40,320,257,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,257,1] 13 (by decide) (choices 1) [4,16,128] r5211 c5211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1882
  · exact u1883
  · exact u1884

def b5212 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 36, targets := 449 }], pairs := [(2,0),(2,6),(2,7),(2,8)], upper := (rows 35 194 44 328 273 36 209 145 401), lower := (rows 35 194 44 328 273 36 64 128 256), losses := [] }

theorem u5212 : Upper (D 9) (R 9) [34,192,40,320,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5212 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5213 : Route 9 := (fun mask => (mask,id))

def c5213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5213 : Upper (D 9) (R 9) [34,192,40,320,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,257,16] 13 (by decide) (choices 1) [1,4,128] r5213 c5213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1885
  · exact u1886
  · exact u1887

def b5214 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 328 273 160 85 149 277), lower := (rows 35 194 44 328 273 160 64 128 256), losses := [] }

theorem u5214 : Upper (D 9) (R 9) [34,192,40,320,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5214 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5215 : Route 9 := (fun mask => (mask,id))

def c5215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5215 : Upper (D 9) (R 9) [34,192,40,320,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,260,1] 13 (by decide) (choices 1) [1,16,128] r5215 c5215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1888
  · exact u1889
  · exact u1890

def b5216 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 52, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(4,0)], upper := (rows 35 194 44 328 276 48 193 129 385), lower := (rows 35 194 44 328 276 48 64 128 256), losses := [] }

theorem u5216 : Upper (D 9) (R 9) [34,192,40,320,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5216 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5217 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 328 276 160 81 145 273), lower := (rows 35 194 44 328 276 160 64 128 256), losses := [] }

theorem u5217 : Upper (D 9) (R 9) [34,192,40,320,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5217 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5218 : Route 9 := (fun mask => (mask,id))

def c5218 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5218 : Upper (D 9) (R 9) [34,192,40,320,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,384,1] 13 (by decide) (choices 1) [1,4,16] r5218 c5218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1891
  · exact u1892
  · exact u1893

def b5219 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 36, targets := 449 }], pairs := [(2,0),(2,6),(2,7),(2,8)], upper := (rows 35 194 44 328 400 36 81 145 273), lower := (rows 35 194 44 328 400 36 64 128 256), losses := [] }

theorem u5219 : Upper (D 9) (R 9) [34,192,40,320,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5219 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u5219
end Delivery.IrregularNine14.P09
