import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0089

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18480 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 134 104 274 33 68 196 324), lower := (rows 25 35 134 104 274 33 64 128 256), losses := [] }

theorem u18480 : Upper (D 6) (R 6) [24,33,130,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18481 : Route 9 := (fun mask => (mask,id))

def c18481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18481 : Upper (D 6) (R 6) [24,33,130,96,258,4] 13 := by
  apply FastRouting.sound _ _ [24,33,130,96,258,4] 13 (by decide) (choices 1) [1,4] r18481 c18481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5384
  · exact u5385

def b18482 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 35 134 104 274 96 69 133 261), lower := (rows 25 35 134 104 274 96 64 128 256), losses := [] }

theorem u18482 : Upper (D 6) (R 6) [24,33,130,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18483 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 134 104 276 33 70 198 326), lower := (rows 25 35 134 104 276 33 64 128 256), losses := [] }

theorem u18483 : Upper (D 6) (R 6) [24,33,130,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18484 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 134 104 276 34 69 197 325), lower := (rows 25 35 134 104 276 34 64 128 256), losses := [] }

theorem u18484 : Upper (D 6) (R 6) [24,33,130,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18485 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 72, targets := 4 }], pairs := [(2,5),(3,2),(4,5)], upper := (rows 25 35 134 104 276 36 67 195 323), lower := (rows 25 35 134 104 276 36 64 128 256), losses := [] }

theorem u18485 : Upper (D 6) (R 6) [24,33,130,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18486 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 35 134 104 276 96 71 135 263), lower := (rows 25 35 134 104 276 96 64 128 256), losses := [] }

theorem u18486 : Upper (D 6) (R 6) [24,33,130,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18487 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 164 13 82 34 324 452 324), lower := (rows 25 35 164 13 82 34 64 128 256), losses := [] }

theorem u18487 : Upper (D 6) (R 6) [24,33,160,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18488 : PairBound 9 := { available := 322, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 13 82 36 322 450 322), lower := (rows 25 35 164 13 82 36 64 128 256), losses := [] }

theorem u18488 : Upper (D 6) (R 6) [24,33,160,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18489 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 388, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 25 35 164 13 82 96 326 390 262), lower := (rows 25 35 164 13 82 96 64 128 256), losses := [] }

theorem u18489 : Upper (D 6) (R 6) [24,33,160,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18490 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 25 35 164 13 82 288 70 198 326), lower := (rows 25 35 164 13 82 288 64 128 256), losses := [] }

theorem u18490 : Upper (D 6) (R 6) [24,33,160,5,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18490 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18491 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 164 13 274 34 68 196 324), lower := (rows 25 35 164 13 274 34 64 128 256), losses := [] }

theorem u18491 : Upper (D 6) (R 6) [24,33,160,5,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18492 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 13 274 36 66 194 322), lower := (rows 25 35 164 13 274 36 64 128 256), losses := [] }

theorem u18492 : Upper (D 6) (R 6) [24,33,160,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18493 : Route 9 := (fun mask => (mask,id))

def c18493 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18493 : Upper (D 6) (R 6) [24,33,160,5,258,64] 13 := by
  apply FastRouting.sound _ _ [24,33,160,5,258,64] 13 (by decide) (choices 1) [2,4] r18493 c18493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5386
  · exact u5387

def b18494 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 164 13 336 34 70 198 326), lower := (rows 25 35 164 13 336 34 64 128 256), losses := [] }

theorem u18494 : Upper (D 6) (R 6) [24,33,160,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18495 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 13 336 36 66 194 322), lower := (rows 25 35 164 13 336 36 64 128 256), losses := [] }

theorem u18495 : Upper (D 6) (R 6) [24,33,160,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18496 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 25 35 164 13 336 96 70 134 262), lower := (rows 25 35 164 13 336 96 64 128 256), losses := [] }

theorem u18496 : Upper (D 6) (R 6) [24,33,160,5,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18497 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 164 14 336 33 70 198 326), lower := (rows 25 35 164 14 336 33 64 128 256), losses := [] }

theorem u18497 : Upper (D 6) (R 6) [24,33,160,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18498 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 337, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 35 164 14 336 34 69 197 325), lower := (rows 25 35 164 14 336 34 64 128 256), losses := [] }

theorem u18498 : Upper (D 6) (R 6) [24,33,160,6,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18499 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 337, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 35 164 14 336 36 67 195 323), lower := (rows 25 35 164 14 336 36 64 128 256), losses := [] }

theorem u18499 : Upper (D 6) (R 6) [24,33,160,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18500 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 140, targets := 64 },{ cop := 3, region := 337, targets := 32 }], pairs := [(0,5),(2,6),(3,6)], upper := (rows 25 35 164 14 336 96 71 135 263), lower := (rows 25 35 164 14 336 96 64 128 256), losses := [] }

theorem u18500 : Upper (D 6) (R 6) [24,33,160,6,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18501 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 164 73 274 34 68 196 324), lower := (rows 25 35 164 73 274 34 64 128 256), losses := [] }

theorem u18501 : Upper (D 6) (R 6) [24,33,160,65,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18502 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 73 274 36 70 198 326), lower := (rows 25 35 164 73 274 36 64 128 256), losses := [] }

theorem u18502 : Upper (D 6) (R 6) [24,33,160,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18503 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 404, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 25 35 164 73 274 96 70 134 262), lower := (rows 25 35 164 73 274 96 64 128 256), losses := [] }

theorem u18503 : Upper (D 6) (R 6) [24,33,160,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18504 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 164 73 276 34 70 198 326), lower := (rows 25 35 164 73 276 34 64 128 256), losses := [] }

theorem u18504 : Upper (D 6) (R 6) [24,33,160,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18505 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 73 276 36 66 194 322), lower := (rows 25 35 164 73 276 36 64 128 256), losses := [] }

theorem u18505 : Upper (D 6) (R 6) [24,33,160,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18506 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 404, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 25 35 164 73 276 96 70 134 262), lower := (rows 25 35 164 73 276 96 64 128 256), losses := [] }

theorem u18506 : Upper (D 6) (R 6) [24,33,160,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18507 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 164 74 84 33 326 390 262), lower := (rows 25 35 164 74 84 33 64 128 256), losses := [] }

theorem u18507 : Upper (D 6) (R 6) [24,33,160,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18508 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 164 74 84 34 325 389 261), lower := (rows 25 35 164 74 84 34 64 128 256), losses := [] }

theorem u18508 : Upper (D 6) (R 6) [24,33,160,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18509 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 74 84 36 323 387 259), lower := (rows 25 35 164 74 84 36 64 128 256), losses := [] }

theorem u18509 : Upper (D 6) (R 6) [24,33,160,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18510 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 25 35 164 74 84 288 71 135 263), lower := (rows 25 35 164 74 84 288 64 128 256), losses := [] }

theorem u18510 : Upper (D 6) (R 6) [24,33,160,66,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18510 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18511 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 164 74 273 34 68 196 324), lower := (rows 25 35 164 74 273 34 64 128 256), losses := [] }

theorem u18511 : Upper (D 6) (R 6) [24,33,160,66,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18512 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 74 273 36 70 198 326), lower := (rows 25 35 164 74 273 36 64 128 256), losses := [] }

theorem u18512 : Upper (D 6) (R 6) [24,33,160,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18513 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 25 35 164 74 273 96 70 134 262), lower := (rows 25 35 164 74 273 96 64 128 256), losses := [] }

theorem u18513 : Upper (D 6) (R 6) [24,33,160,66,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18514 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 164 74 274 33 68 196 324), lower := (rows 25 35 164 74 274 33 64 128 256), losses := [] }

theorem u18514 : Upper (D 6) (R 6) [24,33,160,66,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18515 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 74 274 36 69 197 325), lower := (rows 25 35 164 74 274 36 64 128 256), losses := [] }

theorem u18515 : Upper (D 6) (R 6) [24,33,160,66,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18516 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 25 35 164 74 274 96 69 133 261), lower := (rows 25 35 164 74 274 96 64 128 256), losses := [] }

theorem u18516 : Upper (D 6) (R 6) [24,33,160,66,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18517 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 164 74 276 33 70 198 326), lower := (rows 25 35 164 74 276 33 64 128 256), losses := [] }

theorem u18517 : Upper (D 6) (R 6) [24,33,160,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18518 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 164 74 276 34 69 197 325), lower := (rows 25 35 164 74 276 34 64 128 256), losses := [] }

theorem u18518 : Upper (D 6) (R 6) [24,33,160,66,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18519 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 74 276 36 67 195 323), lower := (rows 25 35 164 74 276 36 64 128 256), losses := [] }

theorem u18519 : Upper (D 6) (R 6) [24,33,160,66,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18520 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 404, targets := 64 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 25 35 164 74 276 96 71 135 263), lower := (rows 25 35 164 74 276 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 104 64 128 256), good := (rows 59 35 160 106 272 96 96 128 256) }] }

theorem u18520 : Upper (D 6) (R 6) [24,33,160,66,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18521 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 164 74 336 33 70 134 262), lower := (rows 25 35 164 74 336 33 64 128 256), losses := [] }

theorem u18521 : Upper (D 6) (R 6) [24,33,160,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18522 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 164 74 336 34 69 133 261), lower := (rows 25 35 164 74 336 34 64 128 256), losses := [] }

theorem u18522 : Upper (D 6) (R 6) [24,33,160,66,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18523 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 74 336 36 71 135 263), lower := (rows 25 35 164 74 336 36 64 128 256), losses := [] }

theorem u18523 : Upper (D 6) (R 6) [24,33,160,66,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18524 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 164 76 273 34 70 198 326), lower := (rows 25 35 164 76 273 34 64 128 256), losses := [] }

theorem u18524 : Upper (D 6) (R 6) [24,33,160,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18525 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 76 273 36 66 194 322), lower := (rows 25 35 164 76 273 36 64 128 256), losses := [] }

theorem u18525 : Upper (D 6) (R 6) [24,33,160,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18526 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 25 35 164 76 273 96 70 134 262), lower := (rows 25 35 164 76 273 96 64 128 256), losses := [] }

theorem u18526 : Upper (D 6) (R 6) [24,33,160,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18527 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 164 76 274 33 70 198 326), lower := (rows 25 35 164 76 274 33 64 128 256), losses := [] }

theorem u18527 : Upper (D 6) (R 6) [24,33,160,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18528 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 164 76 274 34 69 197 325), lower := (rows 25 35 164 76 274 34 64 128 256), losses := [] }

theorem u18528 : Upper (D 6) (R 6) [24,33,160,68,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18529 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 76 274 36 67 195 323), lower := (rows 25 35 164 76 274 36 64 128 256), losses := [] }

theorem u18529 : Upper (D 6) (R 6) [24,33,160,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18530 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 404, targets := 64 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 25 35 164 76 274 96 71 135 263), lower := (rows 25 35 164 76 274 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 104 64 128 256), good := (rows 59 35 160 104 274 96 96 128 256) }] }

theorem u18530 : Upper (D 6) (R 6) [24,33,160,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18531 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 164 76 276 33 66 194 322), lower := (rows 25 35 164 76 276 33 64 128 256), losses := [] }

theorem u18531 : Upper (D 6) (R 6) [24,33,160,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18532 : Route 9 := (fun mask => (mask,id))

def c18532 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18532 : Upper (D 6) (R 6) [24,33,160,68,260,2] 13 := by
  apply FastRouting.sound _ _ [24,33,160,68,260,2] 13 (by decide) (choices 1) [1,2] r18532 c18532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5388
  · exact u5389

def b18533 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 25 35 164 76 276 96 67 131 259), lower := (rows 25 35 164 76 276 96 64 128 256), losses := [] }

theorem u18533 : Upper (D 6) (R 6) [24,33,160,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18534 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 164 76 336 33 70 134 262), lower := (rows 25 35 164 76 336 33 64 128 256), losses := [] }

theorem u18534 : Upper (D 6) (R 6) [24,33,160,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18535 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(1,6),(2,6)], upper := (rows 25 35 164 76 336 34 71 135 263), lower := (rows 25 35 164 76 336 34 64 128 256), losses := [] }

theorem u18535 : Upper (D 6) (R 6) [24,33,160,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18536 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 35 164 76 336 36 67 131 259), lower := (rows 25 35 164 76 336 36 64 128 256), losses := [] }

theorem u18536 : Upper (D 6) (R 6) [24,33,160,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18537 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 196 13 274 34 100 228 356), lower := (rows 25 35 196 13 274 34 64 128 256), losses := [] }

theorem u18537 : Upper (D 6) (R 6) [24,33,192,5,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18538 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 336, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 35 196 13 274 36 98 226 354), lower := (rows 25 35 196 13 274 36 64 128 256), losses := [] }

theorem u18538 : Upper (D 6) (R 6) [24,33,192,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18539 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 25 35 196 13 274 96 102 166 294), lower := (rows 25 35 196 13 274 96 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 100 64 128 256), good := (rows 27 35 224 43 274 96 96 128 256) }] }

theorem u18539 : Upper (D 6) (R 6) [24,33,192,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18539
end Delivery.IrregularNine14.P06
