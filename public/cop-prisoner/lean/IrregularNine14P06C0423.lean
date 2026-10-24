import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0130
import IrregularNine14P06C0131

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25380 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 386 100 25 88 36 71 135 263), lower := (rows 35 386 100 25 88 36 64 128 256), losses := [] }

theorem u25380 : Upper (D 6) (R 6) [34,384,96,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25381 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 386 100 26 28 33 69 197 325), lower := (rows 35 386 100 26 28 33 64 128 256), losses := [] }

theorem u25381 : Upper (D 6) (R 6) [34,384,96,18,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25382 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 450, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 386 100 26 28 36 65 193 321), lower := (rows 35 386 100 26 28 36 64 128 256), losses := [] }

theorem u25382 : Upper (D 6) (R 6) [34,384,96,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25383 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 100 26 28 96 69 133 261), lower := (rows 35 386 100 26 28 96 64 128 256), losses := [] }

theorem u25383 : Upper (D 6) (R 6) [34,384,96,18,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25384 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 36, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 386 100 26 81 33 76 140 268), lower := (rows 35 386 100 26 81 33 64 128 256), losses := [] }

theorem u25384 : Upper (D 6) (R 6) [34,384,96,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25385 : Route 9 := (fun mask => (mask,id))

def c25385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25385 : Upper (D 6) (R 6) [34,384,96,18,65,4] 13 := by
  apply FastRouting.sound _ _ [34,384,96,18,65,4] 13 (by decide) (choices 1) [1,4,8] r25385 c25385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7850
  · exact u7851
  · exact u7852

def b25386 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 386 100 26 81 40 69 133 261), lower := (rows 35 386 100 26 81 40 64 128 256), losses := [] }

theorem u25386 : Upper (D 6) (R 6) [34,384,96,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25386 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25387 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 386, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 386 100 28 81 33 78 142 270), lower := (rows 35 386 100 28 81 33 64 128 256), losses := [] }

theorem u25387 : Upper (D 6) (R 6) [34,384,96,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25388 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 100 28 81 34 77 141 269), lower := (rows 35 386 100 28 81 34 64 128 256), losses := [] }

theorem u25388 : Upper (D 6) (R 6) [34,384,96,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25389 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 386 100 28 81 36 75 139 267), lower := (rows 35 386 100 28 81 36 64 128 256), losses := [] }

theorem u25389 : Upper (D 6) (R 6) [34,384,96,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25390 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 386 100 28 81 40 71 135 263), lower := (rows 35 386 100 28 81 40 64 128 256), losses := [] }

theorem u25390 : Upper (D 6) (R 6) [34,384,96,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25390 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25391 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 419, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 386 100 28 82 33 77 141 269), lower := (rows 35 386 100 28 82 33 64 128 256), losses := [] }

theorem u25391 : Upper (D 6) (R 6) [34,384,96,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25392 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 386 100 28 82 36 73 137 265), lower := (rows 35 386 100 28 82 36 64 128 256), losses := [] }

theorem u25392 : Upper (D 6) (R 6) [34,384,96,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25393 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 386 100 28 82 40 69 133 261), lower := (rows 35 386 100 28 82 40 64 128 256), losses := [] }

theorem u25393 : Upper (D 6) (R 6) [34,384,96,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25393 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25394 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 133 14 81 34 324 452 324), lower := (rows 41 50 133 14 81 34 64 128 256), losses := [] }

theorem u25394 : Upper (D 6) (R 6) [40,48,129,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25395 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 133 14 81 36 322 450 322), lower := (rows 41 50 133 14 81 36 64 128 256), losses := [] }

theorem u25395 : Upper (D 6) (R 6) [40,48,129,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25396 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 50 133 14 81 96 326 390 262), lower := (rows 41 50 133 14 81 96 64 128 256), losses := [] }

theorem u25396 : Upper (D 6) (R 6) [40,48,129,6,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25397 : PairBound 9 := { available := 70, camps := [], pairs := [(1,0),(2,5)], upper := (rows 41 50 133 14 81 288 70 198 326), lower := (rows 41 50 133 14 81 288 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 297 72 136 264), good := (rows 488 50 164 494 114 288 64 128 288) },{ target := 5, region := (rows 1 2 5 8 17 0 72 136 264), good := (rows 477 18 149 462 85 256 64 128 256) }] }

theorem u25397 : Upper (D 6) (R 6) [40,48,129,6,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25397 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25398 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 41 50 133 14 84 33 322 450 322), lower := (rows 41 50 133 14 84 33 64 128 256), losses := [] }

theorem u25398 : Upper (D 6) (R 6) [40,48,129,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25399 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 133 14 84 34 321 449 321), lower := (rows 41 50 133 14 84 34 64 128 256), losses := [] }

theorem u25399 : Upper (D 6) (R 6) [40,48,129,6,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25400 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 50 133 14 84 96 323 387 259), lower := (rows 41 50 133 14 84 96 64 128 256), losses := [] }

theorem u25400 : Upper (D 6) (R 6) [40,48,129,6,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25401 : Route 9 := (fun mask => (mask,id))

def c25401 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25401 : Upper (D 6) (R 6) [40,48,129,6,68,256] 13 := by
  apply FastRouting.sound _ _ [40,48,129,6,68,256] 13 (by decide) (choices 1) [1,2] r25401 c25401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7853
  · exact u7854

def b25402 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 133 14 273 34 68 196 324), lower := (rows 41 50 133 14 273 34 64 128 256), losses := [] }

theorem u25402 : Upper (D 6) (R 6) [40,48,129,6,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25403 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 133 14 273 36 66 194 322), lower := (rows 41 50 133 14 273 36 64 128 256), losses := [] }

theorem u25403 : Upper (D 6) (R 6) [40,48,129,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25404 : PairBound 9 := { available := 70, camps := [], pairs := [(1,0),(2,5),(4,5)], upper := (rows 41 50 133 14 273 96 70 198 326), lower := (rows 41 50 133 14 273 96 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 105 72 136 264), good := (rows 488 50 164 494 306 96 96 128 256) },{ target := 5, region := (rows 1 2 5 8 17 0 72 136 264), good := (rows 477 18 149 462 277 64 64 128 256) }] }

theorem u25404 : Upper (D 6) (R 6) [40,48,129,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25405 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 41 50 133 14 276 33 66 194 322), lower := (rows 41 50 133 14 276 33 64 128 256), losses := [] }

theorem u25405 : Upper (D 6) (R 6) [40,48,129,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25406 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 133 14 276 34 65 193 321), lower := (rows 41 50 133 14 276 34 64 128 256), losses := [] }

theorem u25406 : Upper (D 6) (R 6) [40,48,129,6,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25407 : Route 9 := (fun mask => (mask,id))

def c25407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25407 : Upper (D 6) (R 6) [40,48,129,6,260,64] 13 := by
  apply FastRouting.sound _ _ [40,48,129,6,260,64] 13 (by decide) (choices 1) [1,2] r25407 c25407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7855
  · exact u7856

def b25408 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 133 14 336 33 70 198 326), lower := (rows 41 50 133 14 336 33 64 128 256), losses := [] }

theorem u25408 : Upper (D 6) (R 6) [40,48,129,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25409 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 133 14 336 34 69 197 325), lower := (rows 41 50 133 14 336 34 64 128 256), losses := [] }

theorem u25409 : Upper (D 6) (R 6) [40,48,129,6,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25410 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 133 14 336 36 67 195 323), lower := (rows 41 50 133 14 336 36 64 128 256), losses := [] }

theorem u25410 : Upper (D 6) (R 6) [40,48,129,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25411 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 50 133 14 336 96 71 135 263), lower := (rows 41 50 133 14 336 96 64 128 256), losses := [] }

theorem u25411 : Upper (D 6) (R 6) [40,48,129,6,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25412 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 50 133 73 22 34 324 452 324), lower := (rows 41 50 133 73 22 34 64 128 256), losses := [] }

theorem u25412 : Upper (D 6) (R 6) [40,48,129,65,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25413 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 2, region := 50, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 50 133 73 22 36 322 450 322), lower := (rows 41 50 133 73 22 36 64 128 256), losses := [] }

theorem u25413 : Upper (D 6) (R 6) [40,48,129,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25414 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 50 133 73 22 96 326 390 262), lower := (rows 41 50 133 73 22 96 64 128 256), losses := [] }

theorem u25414 : Upper (D 6) (R 6) [40,48,129,65,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25415 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 41 50 133 73 22 288 70 198 326), lower := (rows 41 50 133 73 22 288 64 128 256), losses := [] }

theorem u25415 : Upper (D 6) (R 6) [40,48,129,65,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25415 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25416 : PairBound 9 := { available := 68, camps := [{ cop := 8, region := 50, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 133 73 274 34 68 196 324), lower := (rows 41 50 133 73 274 34 64 128 256), losses := [] }

theorem u25416 : Upper (D 6) (R 6) [40,48,129,65,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25417 : Route 9 := (fun mask => (mask,id))

def c25417 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25417 : Upper (D 6) (R 6) [40,48,129,65,258,4] 13 := by
  apply FastRouting.sound _ _ [40,48,129,65,258,4] 13 (by decide) (choices 1) [2,4] r25417 c25417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7857
  · exact u7858

def b25418 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 50 133 73 274 96 70 134 262), lower := (rows 41 50 133 73 274 96 64 128 256), losses := [] }

theorem u25418 : Upper (D 6) (R 6) [40,48,129,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25419 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 50 133 73 276 34 70 198 326), lower := (rows 41 50 133 73 276 34 64 128 256), losses := [] }

theorem u25419 : Upper (D 6) (R 6) [40,48,129,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25420 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 2, region := 370, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 50 133 73 276 36 66 194 322), lower := (rows 41 50 133 73 276 36 64 128 256), losses := [] }

theorem u25420 : Upper (D 6) (R 6) [40,48,129,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25421 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 50 133 73 276 96 70 134 262), lower := (rows 41 50 133 73 276 96 64 128 256), losses := [] }

theorem u25421 : Upper (D 6) (R 6) [40,48,129,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25422 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 50 133 73 336 34 70 134 262), lower := (rows 41 50 133 73 336 34 64 128 256), losses := [] }

theorem u25422 : Upper (D 6) (R 6) [40,48,129,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25423 : Route 9 := (fun mask => (mask,id))

def c25423 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25423 : Upper (D 6) (R 6) [40,48,129,65,320,4] 13 := by
  apply FastRouting.sound _ _ [40,48,129,65,320,4] 13 (by decide) (choices 1) [2,4] r25423 c25423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7859
  · exact u7860

def b25424 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 50 133 74 84 33 326 390 262), lower := (rows 41 50 133 74 84 33 64 128 256), losses := [] }

theorem u25424 : Upper (D 6) (R 6) [40,48,129,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25425 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 133 74 84 34 325 389 261), lower := (rows 41 50 133 74 84 34 64 128 256), losses := [] }

theorem u25425 : Upper (D 6) (R 6) [40,48,129,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25426 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 133 74 84 36 323 387 259), lower := (rows 41 50 133 74 84 36 64 128 256), losses := [] }

theorem u25426 : Upper (D 6) (R 6) [40,48,129,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25427 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 50 133 74 84 288 71 135 263), lower := (rows 41 50 133 74 84 288 64 128 256), losses := [] }

theorem u25427 : Upper (D 6) (R 6) [40,48,129,66,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25427 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25428 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 133 74 273 34 68 196 324), lower := (rows 41 50 133 74 273 34 64 128 256), losses := [] }

theorem u25428 : Upper (D 6) (R 6) [40,48,129,66,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25429 : Route 9 := (fun mask => (mask,id))

def c25429 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25429 : Upper (D 6) (R 6) [40,48,129,66,257,4] 13 := by
  apply FastRouting.sound _ _ [40,48,129,66,257,4] 13 (by decide) (choices 1) [2,4] r25429 c25429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7861
  · exact u7862

def b25430 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 50 133 74 273 96 70 134 262), lower := (rows 41 50 133 74 273 96 64 128 256), losses := [] }

theorem u25430 : Upper (D 6) (R 6) [40,48,129,66,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25431 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 133 74 276 33 70 198 326), lower := (rows 41 50 133 74 276 33 64 128 256), losses := [] }

theorem u25431 : Upper (D 6) (R 6) [40,48,129,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25432 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 133 74 276 34 69 197 325), lower := (rows 41 50 133 74 276 34 64 128 256), losses := [] }

theorem u25432 : Upper (D 6) (R 6) [40,48,129,66,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25433 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 50 133 74 276 36 67 195 323), lower := (rows 41 50 133 74 276 36 64 128 256), losses := [] }

theorem u25433 : Upper (D 6) (R 6) [40,48,129,66,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25434 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 50 133 74 276 96 71 135 263), lower := (rows 41 50 133 74 276 96 64 128 256), losses := [] }

theorem u25434 : Upper (D 6) (R 6) [40,48,129,66,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25435 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 50 133 74 336 33 70 134 262), lower := (rows 41 50 133 74 336 33 64 128 256), losses := [] }

theorem u25435 : Upper (D 6) (R 6) [40,48,129,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25436 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 133 74 336 34 69 133 261), lower := (rows 41 50 133 74 336 34 64 128 256), losses := [] }

theorem u25436 : Upper (D 6) (R 6) [40,48,129,66,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25437 : Route 9 := (fun mask => (mask,id))

def c25437 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25437 : Upper (D 6) (R 6) [40,48,129,66,320,4] 13 := by
  apply FastRouting.sound _ _ [40,48,129,66,320,4] 13 (by decide) (choices 1) [1,2,4] r25437 c25437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7863
  · exact u7864
  · exact u7865

def b25438 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 41 50 133 76 22 33 322 450 322), lower := (rows 41 50 133 76 22 33 64 128 256), losses := [] }

theorem u25438 : Upper (D 6) (R 6) [40,48,129,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25439 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 50 133 76 22 34 321 449 321), lower := (rows 41 50 133 76 22 34 64 128 256), losses := [] }

theorem u25439 : Upper (D 6) (R 6) [40,48,129,68,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25439
end Delivery.IrregularNine14.P06
