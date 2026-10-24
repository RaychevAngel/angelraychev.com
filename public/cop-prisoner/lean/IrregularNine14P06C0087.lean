import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0006

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5220 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 162 324 13 112 36 80 131 259), lower := (rows 11 162 324 13 112 36 80 128 256), losses := [] }

theorem u5220 : Upper (D 6) (R 6) [10,160,320,5,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5220 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5221 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 5, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 162 324 28 49 96 65 134 262), lower := (rows 11 162 324 28 49 96 65 128 256), losses := [] }

theorem u5221 : Upper (D 6) (R 6) [10,160,320,20,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5222 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 98, targets := 5 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 11 162 324 28 49 96 66 133 261), lower := (rows 11 162 324 28 49 96 66 128 256), losses := [] }

theorem u5222 : Upper (D 6) (R 6) [10,160,320,20,33,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5223 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 130, targets := 68 },{ cop := 8, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 11 162 324 28 49 96 68 131 259), lower := (rows 11 162 324 28 49 96 68 128 256), losses := [] }

theorem u5223 : Upper (D 6) (R 6) [10,160,320,20,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5224 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 162 324 28 81 36 65 162 290), lower := (rows 11 162 324 28 81 36 65 128 256), losses := [] }

theorem u5224 : Upper (D 6) (R 6) [10,160,320,20,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5225 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 162 324 28 81 36 66 161 289), lower := (rows 11 162 324 28 81 36 66 128 256), losses := [] }

theorem u5225 : Upper (D 6) (R 6) [10,160,320,20,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5226 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 11 162 324 28 81 36 96 131 259), lower := (rows 11 162 324 28 81 36 96 128 256), losses := [] }

theorem u5226 : Upper (D 6) (R 6) [10,160,320,20,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5227 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 260, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 324 44 81 33 66 148 276), lower := (rows 11 162 324 44 81 33 66 128 256), losses := [] }

theorem u5227 : Upper (D 6) (R 6) [10,160,320,36,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5228 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 324 44 81 33 68 146 274), lower := (rows 11 162 324 44 81 33 68 128 256), losses := [] }

theorem u5228 : Upper (D 6) (R 6) [10,160,320,36,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5229 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 324 44 81 33 80 134 262), lower := (rows 11 162 324 44 81 33 80 128 256), losses := [] }

theorem u5229 : Upper (D 6) (R 6) [10,160,320,36,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5229 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5230 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 260, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 324 44 82 33 65 148 276), lower := (rows 11 162 324 44 82 33 65 128 256), losses := [] }

theorem u5230 : Upper (D 6) (R 6) [10,160,320,36,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5231 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 324 44 82 33 68 145 273), lower := (rows 11 162 324 44 82 33 68 128 256), losses := [] }

theorem u5231 : Upper (D 6) (R 6) [10,160,320,36,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5232 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 162 324 44 82 33 80 133 261), lower := (rows 11 162 324 44 82 33 80 128 256), losses := [] }

theorem u5232 : Upper (D 6) (R 6) [10,160,320,36,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5232 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5233 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 324 56 81 36 65 134 262), lower := (rows 11 162 324 56 81 36 65 128 256), losses := [] }

theorem u5233 : Upper (D 6) (R 6) [10,160,320,48,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5234 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 324 56 81 36 66 133 261), lower := (rows 11 162 324 56 81 36 66 128 256), losses := [] }

theorem u5234 : Upper (D 6) (R 6) [10,160,320,48,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5235 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 324 56 81 36 68 131 259), lower := (rows 11 162 324 56 81 36 68 128 256), losses := [] }

theorem u5235 : Upper (D 6) (R 6) [10,160,320,48,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5236 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 324 73 22 36 65 176 304), lower := (rows 11 162 324 73 22 36 65 128 256), losses := [] }

theorem u5236 : Upper (D 6) (R 6) [10,160,320,65,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5237 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 324 73 22 36 80 161 289), lower := (rows 11 162 324 73 22 36 80 128 256), losses := [] }

theorem u5237 : Upper (D 6) (R 6) [10,160,320,65,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5237 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5238 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 162 324 73 22 36 96 145 273), lower := (rows 11 162 324 73 22 36 96 128 256), losses := [] }

theorem u5238 : Upper (D 6) (R 6) [10,160,320,65,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5239 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 324 73 22 48 65 164 292), lower := (rows 11 162 324 73 22 48 65 128 256), losses := [] }

theorem u5239 : Upper (D 6) (R 6) [10,160,320,65,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5239 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5240 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 162 324 73 22 48 68 161 289), lower := (rows 11 162 324 73 22 48 68 128 256), losses := [] }

theorem u5240 : Upper (D 6) (R 6) [10,160,320,65,6,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5240 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5241 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 162 324 73 22 48 96 133 261), lower := (rows 11 162 324 73 22 48 96 128 256), losses := [] }

theorem u5241 : Upper (D 6) (R 6) [10,160,320,65,6,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5241 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5242 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 324 73 49 36 66 148 276), lower := (rows 11 162 324 73 49 36 66 128 256), losses := [] }

theorem u5242 : Upper (D 6) (R 6) [10,160,320,65,33,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5243 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 454, targets := 1 },{ cop := 4, region := 130, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 162 324 73 49 36 68 146 274), lower := (rows 11 162 324 73 49 36 68 128 256), losses := [] }

theorem u5243 : Upper (D 6) (R 6) [10,160,320,65,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5244 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 162 324 73 49 36 80 134 262), lower := (rows 11 162 324 73 49 36 80 128 256), losses := [] }

theorem u5244 : Upper (D 6) (R 6) [10,160,320,65,33,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5244 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5245 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 324 88 21 36 65 162 290), lower := (rows 11 162 324 88 21 36 65 128 256), losses := [] }

theorem u5245 : Upper (D 6) (R 6) [10,160,320,80,5,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5246 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6),(2,1),(3,0)], upper := (rows 11 162 324 88 21 36 66 161 289), lower := (rows 11 162 324 88 21 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 52 67 128 256), good := (rows 74 226 356 120 124 36 66 128 256) },{ target := 1, region := (rows 1 0 12 8 17 61 64 145 273), good := (rows 445 160 356 508 437 36 64 128 256) }] }

theorem u5246 : Upper (D 6) (R 6) [10,160,320,80,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5247 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 162 324 88 21 36 96 131 259), lower := (rows 11 162 324 88 21 36 96 128 256), losses := [] }

theorem u5247 : Upper (D 6) (R 6) [10,160,320,80,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5248 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 73, targets := 4 },{ cop := 4, region := 73, targets := 32 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 324 88 22 33 65 164 292), lower := (rows 11 162 324 88 22 33 65 128 256), losses := [] }

theorem u5248 : Upper (D 6) (R 6) [10,160,320,80,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5249 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 324 88 22 33 68 161 289), lower := (rows 11 162 324 88 22 33 68 128 256), losses := [] }

theorem u5249 : Upper (D 6) (R 6) [10,160,320,80,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5250 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 105, targets := 4 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 11 162 324 88 22 33 96 133 261), lower := (rows 11 162 324 88 22 33 96 128 256), losses := [] }

theorem u5250 : Upper (D 6) (R 6) [10,160,320,80,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5251 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 324 88 49 36 65 134 262), lower := (rows 11 162 324 88 49 36 65 128 256), losses := [] }

theorem u5251 : Upper (D 6) (R 6) [10,160,320,80,33,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5252 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 324 88 49 36 66 133 261), lower := (rows 11 162 324 88 49 36 66 128 256), losses := [] }

theorem u5252 : Upper (D 6) (R 6) [10,160,320,80,33,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5253 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 130, targets := 68 },{ cop := 8, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 11 162 324 88 49 36 68 131 259), lower := (rows 11 162 324 88 49 36 68 128 256), losses := [] }

theorem u5253 : Upper (D 6) (R 6) [10,160,320,80,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5254 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 130, targets := 65 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,0),(1,6),(2,5)], upper := (rows 11 162 324 88 52 33 65 134 262), lower := (rows 11 162 324 88 52 33 65 128 256), losses := [] }

theorem u5254 : Upper (D 6) (R 6) [10,160,320,80,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5255 : Route 9 := (fun mask => (mask,id))

def c5255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5255 : Upper (D 6) (R 6) [10,160,320,80,36,1,2] 13 := by
  apply FastRouting.sound _ _ [10,160,320,80,36,1,2] 13 (by decide) (choices 1) [1,4] r5255 c5255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u384
  · exact u385

def b5256 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 324 88 52 33 68 131 259), lower := (rows 11 162 324 88 52 33 68 128 256), losses := [] }

theorem u5256 : Upper (D 6) (R 6) [10,160,320,80,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5257 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 324 104 22 33 65 148 276), lower := (rows 11 162 324 104 22 33 65 128 256), losses := [] }

theorem u5257 : Upper (D 6) (R 6) [10,160,320,96,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5258 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 162 324 104 22 33 68 145 273), lower := (rows 11 162 324 104 22 33 68 128 256), losses := [] }

theorem u5258 : Upper (D 6) (R 6) [10,160,320,96,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5259 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 324 104 22 33 80 133 261), lower := (rows 11 162 324 104 22 33 80 128 256), losses := [] }

theorem u5259 : Upper (D 6) (R 6) [10,160,320,96,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5259 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5260 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 386 22 41 84 33 96 196 324), lower := (rows 11 386 22 41 84 33 96 128 256), losses := [] }

theorem u5260 : Upper (D 6) (R 6) [10,384,18,33,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5261 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 386 22 41 84 36 96 193 321), lower := (rows 11 386 22 41 84 36 96 128 256), losses := [] }

theorem u5261 : Upper (D 6) (R 6) [10,384,18,33,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5262 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 116, targets := 1 },{ cop := 0, region := 104, targets := 2 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 11 386 22 41 84 96 96 133 261), lower := (rows 11 386 22 41 84 96 96 128 256), losses := [] }

theorem u5262 : Upper (D 6) (R 6) [10,384,18,33,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5263 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 22 41 112 36 65 196 324), lower := (rows 11 386 22 41 112 36 65 128 256), losses := [] }

theorem u5263 : Upper (D 6) (R 6) [10,384,18,33,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5264 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 395, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 386 22 41 112 36 68 193 321), lower := (rows 11 386 22 41 112 36 68 128 256), losses := [] }

theorem u5264 : Upper (D 6) (R 6) [10,384,18,33,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5265 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 386 38 25 84 36 65 224 352), lower := (rows 11 386 38 25 84 36 65 128 256), losses := [] }

theorem u5265 : Upper (D 6) (R 6) [10,384,34,17,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5266 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 386 38 25 84 36 96 193 321), lower := (rows 11 386 38 25 84 36 96 128 256), losses := [] }

theorem u5266 : Upper (D 6) (R 6) [10,384,34,17,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5267 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 386 38 25 84 96 65 164 292), lower := (rows 11 386 38 25 84 96 65 128 256), losses := [] }

theorem u5267 : Upper (D 6) (R 6) [10,384,34,17,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5268 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 386 38 25 84 96 68 161 289), lower := (rows 11 386 38 25 84 96 68 128 256), losses := [] }

theorem u5268 : Upper (D 6) (R 6) [10,384,34,17,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5269 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 386 38 25 84 96 96 133 261), lower := (rows 11 386 38 25 84 96 96 128 256), losses := [] }

theorem u5269 : Upper (D 6) (R 6) [10,384,34,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5270 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 386 38 25 112 36 65 196 324), lower := (rows 11 386 38 25 112 36 65 128 256), losses := [] }

theorem u5270 : Upper (D 6) (R 6) [10,384,34,17,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5271 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 386 38 25 112 36 68 193 321), lower := (rows 11 386 38 25 112 36 68 128 256), losses := [] }

theorem u5271 : Upper (D 6) (R 6) [10,384,34,17,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5272 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 386 38 28 81 96 65 164 292), lower := (rows 11 386 38 28 81 96 65 128 256), losses := [] }

theorem u5272 : Upper (D 6) (R 6) [10,384,34,20,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5273 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 386 38 28 81 96 68 161 289), lower := (rows 11 386 38 28 81 96 68 128 256), losses := [] }

theorem u5273 : Upper (D 6) (R 6) [10,384,34,20,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5274 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 387, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 386 38 28 81 96 96 133 261), lower := (rows 11 386 38 28 81 96 96 128 256), losses := [] }

theorem u5274 : Upper (D 6) (R 6) [10,384,34,20,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5275 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 386, targets := 33 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,0),(1,5),(2,6)], upper := (rows 11 386 38 56 84 33 65 196 324), lower := (rows 11 386 38 56 84 33 65 128 256), losses := [] }

theorem u5275 : Upper (D 6) (R 6) [10,384,34,48,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5276 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 386 38 56 84 33 68 193 321), lower := (rows 11 386 38 56 84 33 68 128 256), losses := [] }

theorem u5276 : Upper (D 6) (R 6) [10,384,34,48,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5277 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 386 38 76 81 33 68 176 304), lower := (rows 11 386 38 76 81 33 68 128 256), losses := [] }

theorem u5277 : Upper (D 6) (R 6) [10,384,34,68,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5278 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 386 38 76 81 33 80 164 292), lower := (rows 11 386 38 76 81 33 80 128 256), losses := [] }

theorem u5278 : Upper (D 6) (R 6) [10,384,34,68,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5278 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5279 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 386 38 76 81 33 96 148 276), lower := (rows 11 386 38 76 81 33 96 128 256), losses := [] }

theorem u5279 : Upper (D 6) (R 6) [10,384,34,68,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5279
end Delivery.IrregularNine14.P06
