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

def b18420 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 133 74 336 34 100 164 292), lower := (rows 25 35 133 74 336 34 64 128 256), losses := [] }

theorem u18420 : Upper (D 6) (R 6) [24,33,129,66,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18421 : Route 9 := (fun mask => (mask,id))

def c18421 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18421 : Upper (D 6) (R 6) [24,33,129,66,320,4] 13 := by
  apply FastRouting.sound _ _ [24,33,129,66,320,4] 13 (by decide) (choices 1) [2,4,32] r18421 c18421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5372
  · exact u5373
  · exact u5374

def b18422 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 133 76 274 34 100 228 356), lower := (rows 25 35 133 76 274 34 64 128 256), losses := [] }

theorem u18422 : Upper (D 6) (R 6) [24,33,129,68,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18423 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,2)], upper := (rows 25 35 133 76 274 36 98 226 354), lower := (rows 25 35 133 76 274 36 64 128 256), losses := [] }

theorem u18423 : Upper (D 6) (R 6) [24,33,129,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18424 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 404, targets := 64 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 25 35 133 76 274 96 102 166 294), lower := (rows 25 35 133 76 274 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 104 64 128 256), good := (rows 59 35 131 104 274 96 96 128 256) }] }

theorem u18424 : Upper (D 6) (R 6) [24,33,129,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18425 : Route 9 := (fun mask => (mask,id))

def c18425 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18425 : Upper (D 6) (R 6) [24,33,129,68,260,2] 13 := by
  apply FastRouting.sound _ _ [24,33,129,68,260,2] 13 (by decide) (choices 1) [2,32] r18425 c18425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5375
  · exact u5376

def b18426 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 25 35 133 76 276 96 98 162 290), lower := (rows 25 35 133 76 276 96 64 128 256), losses := [] }

theorem u18426 : Upper (D 6) (R 6) [24,33,129,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18427 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 133 76 304 34 70 198 326), lower := (rows 25 35 133 76 304 34 64 128 256), losses := [] }

theorem u18427 : Upper (D 6) (R 6) [24,33,129,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18428 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,2)], upper := (rows 25 35 133 76 304 36 66 194 322), lower := (rows 25 35 133 76 304 36 64 128 256), losses := [] }

theorem u18428 : Upper (D 6) (R 6) [24,33,129,68,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18429 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 25 35 133 76 304 96 70 134 262), lower := (rows 25 35 133 76 304 96 64 128 256), losses := [] }

theorem u18429 : Upper (D 6) (R 6) [24,33,129,68,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18430 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(1,6),(2,6)], upper := (rows 25 35 133 76 336 34 102 166 294), lower := (rows 25 35 133 76 336 34 64 128 256), losses := [] }

theorem u18430 : Upper (D 6) (R 6) [24,33,129,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18431 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 1, region := 336, targets := 1 }], pairs := [(1,6),(2,6),(4,0)], upper := (rows 25 35 133 76 336 36 98 162 290), lower := (rows 25 35 133 76 336 36 64 128 256), losses := [] }

theorem u18431 : Upper (D 6) (R 6) [24,33,129,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18432 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 133 104 274 34 68 196 324), lower := (rows 25 35 133 104 274 34 64 128 256), losses := [] }

theorem u18432 : Upper (D 6) (R 6) [24,33,129,96,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18433 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 25 35 133 104 274 36 70 198 326), lower := (rows 25 35 133 104 274 36 64 128 256), losses := [] }

theorem u18433 : Upper (D 6) (R 6) [24,33,129,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18434 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 35 133 104 274 96 70 134 262), lower := (rows 25 35 133 104 274 96 64 128 256), losses := [] }

theorem u18434 : Upper (D 6) (R 6) [24,33,129,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18435 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 133 104 276 34 70 198 326), lower := (rows 25 35 133 104 276 34 64 128 256), losses := [] }

theorem u18435 : Upper (D 6) (R 6) [24,33,129,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18436 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 72, targets := 5 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,5),(3,0),(3,2)], upper := (rows 25 35 133 104 276 36 66 194 322), lower := (rows 25 35 133 104 276 36 64 128 256), losses := [] }

theorem u18436 : Upper (D 6) (R 6) [24,33,129,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18437 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 35 133 104 276 96 70 134 262), lower := (rows 25 35 133 104 276 96 64 128 256), losses := [] }

theorem u18437 : Upper (D 6) (R 6) [24,33,129,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18438 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 336, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 35 134 13 82 36 352 480 352), lower := (rows 25 35 134 13 82 36 64 128 256), losses := [] }

theorem u18438 : Upper (D 6) (R 6) [24,33,130,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18439 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 388, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 25 35 134 13 82 96 356 420 292), lower := (rows 25 35 134 13 82 96 64 128 256), losses := [] }

theorem u18439 : Upper (D 6) (R 6) [24,33,130,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18440 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 25 35 134 13 82 288 100 228 356), lower := (rows 25 35 134 13 82 288 64 128 256), losses := [] }

theorem u18440 : Upper (D 6) (R 6) [24,33,130,5,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18440 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18441 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 336, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 35 134 13 274 36 96 224 352), lower := (rows 25 35 134 13 274 36 64 128 256), losses := [] }

theorem u18441 : Upper (D 6) (R 6) [24,33,130,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18442 : Route 9 := (fun mask => (mask,id))

def c18442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18442 : Upper (D 6) (R 6) [24,33,130,5,258,64] 13 := by
  apply FastRouting.sound _ _ [24,33,130,5,258,64] 13 (by decide) (choices 1) [4,32] r18442 c18442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5377
  · exact u5378

def b18443 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 134 13 336 34 100 228 356), lower := (rows 25 35 134 13 336 34 64 128 256), losses := [] }

theorem u18443 : Upper (D 6) (R 6) [24,33,130,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18444 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 336, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 35 134 13 336 36 98 226 354), lower := (rows 25 35 134 13 336 36 64 128 256), losses := [] }

theorem u18444 : Upper (D 6) (R 6) [24,33,130,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18445 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 25 35 134 13 336 96 102 166 294), lower := (rows 25 35 134 13 336 96 64 128 256), losses := [] }

theorem u18445 : Upper (D 6) (R 6) [24,33,130,5,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18446 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 25 35 134 73 274 36 100 228 356), lower := (rows 25 35 134 73 274 36 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 10 16 36 100 164 292), good := (rows 25 489 492 73 281 484 64 128 256) }] }

theorem u18446 : Upper (D 6) (R 6) [24,33,130,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18447 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 404, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 25 35 134 73 274 96 100 164 292), lower := (rows 25 35 134 73 274 96 64 128 256), losses := [] }

theorem u18447 : Upper (D 6) (R 6) [24,33,130,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18448 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 134 73 276 34 100 228 356), lower := (rows 25 35 134 73 276 34 64 128 256), losses := [] }

theorem u18448 : Upper (D 6) (R 6) [24,33,130,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18449 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 72, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 134 73 276 36 98 226 354), lower := (rows 25 35 134 73 276 36 64 128 256), losses := [] }

theorem u18449 : Upper (D 6) (R 6) [24,33,130,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18450 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 404, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 25 35 134 73 276 96 102 166 294), lower := (rows 25 35 134 73 276 96 64 128 256), losses := [] }

theorem u18450 : Upper (D 6) (R 6) [24,33,130,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18451 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 134 74 84 33 356 420 292), lower := (rows 25 35 134 74 84 33 64 128 256), losses := [] }

theorem u18451 : Upper (D 6) (R 6) [24,33,130,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18452 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 1, region := 328, targets := 4 }], pairs := [(1,6),(2,6),(3,2)], upper := (rows 25 35 134 74 84 36 353 417 289), lower := (rows 25 35 134 74 84 36 64 128 256), losses := [] }

theorem u18452 : Upper (D 6) (R 6) [24,33,130,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18453 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 25 35 134 74 84 288 101 165 293), lower := (rows 25 35 134 74 84 288 64 128 256), losses := [] }

theorem u18453 : Upper (D 6) (R 6) [24,33,130,66,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18453 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18454 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(0,1),(2,0),(3,0)], upper := (rows 25 35 134 74 273 36 100 228 356), lower := (rows 25 35 134 74 273 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 18 36 100 164 292), good := (rows 25 497 500 89 273 484 64 128 256) }] }

theorem u18454 : Upper (D 6) (R 6) [24,33,130,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18455 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 25 35 134 74 273 96 100 164 292), lower := (rows 25 35 134 74 273 96 64 128 256), losses := [] }

theorem u18455 : Upper (D 6) (R 6) [24,33,130,66,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18456 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 134 74 276 33 100 228 356), lower := (rows 25 35 134 74 276 33 64 128 256), losses := [] }

theorem u18456 : Upper (D 6) (R 6) [24,33,130,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18457 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 72, targets := 4 }], pairs := [(0,2),(3,2),(4,1)], upper := (rows 25 35 134 74 276 36 97 225 353), lower := (rows 25 35 134 74 276 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 52 67 131 259), good := (rows 505 481 500 456 308 52 64 128 256) },{ target := 2, region := (rows 17 2 0 14 16 32 66 130 258), good := (rows 25 491 458 458 281 40 64 128 256) }] }

theorem u18457 : Upper (D 6) (R 6) [24,33,130,66,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18458 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 404, targets := 64 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 25 35 134 74 276 96 101 165 293), lower := (rows 25 35 134 74 276 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 104 64 128 256), good := (rows 59 35 130 106 272 96 96 128 256) }] }

theorem u18458 : Upper (D 6) (R 6) [24,33,130,66,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18459 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 134 74 304 33 68 196 324), lower := (rows 25 35 134 74 304 33 64 128 256), losses := [] }

theorem u18459 : Upper (D 6) (R 6) [24,33,130,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18460 : Route 9 := (fun mask => (mask,id))

def c18460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18460 : Upper (D 6) (R 6) [24,33,130,66,288,4] 13 := by
  apply FastRouting.sound _ _ [24,33,130,66,288,4] 13 (by decide) (choices 1) [1,4] r18460 c18460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5379
  · exact u5380

def b18461 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 25 35 134 74 304 96 69 133 261), lower := (rows 25 35 134 74 304 96 64 128 256), losses := [] }

theorem u18461 : Upper (D 6) (R 6) [24,33,130,66,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18462 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 134 74 336 33 100 164 292), lower := (rows 25 35 134 74 336 33 64 128 256), losses := [] }

theorem u18462 : Upper (D 6) (R 6) [24,33,130,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18463 : Route 9 := (fun mask => (mask,id))

def c18463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18463 : Upper (D 6) (R 6) [24,33,130,66,320,4] 13 := by
  apply FastRouting.sound _ _ [24,33,130,66,320,4] 13 (by decide) (choices 1) [1,4,32] r18463 c18463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5381
  · exact u5382
  · exact u5383

def b18464 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 134 76 273 34 100 228 356), lower := (rows 25 35 134 76 273 34 64 128 256), losses := [] }

theorem u18464 : Upper (D 6) (R 6) [24,33,130,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18465 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 336, targets := 4 }], pairs := [(2,0),(3,0),(4,2)], upper := (rows 25 35 134 76 273 36 98 226 354), lower := (rows 25 35 134 76 273 36 64 128 256), losses := [] }

theorem u18465 : Upper (D 6) (R 6) [24,33,130,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18466 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 25 35 134 76 273 96 102 166 294), lower := (rows 25 35 134 76 273 96 64 128 256), losses := [] }

theorem u18466 : Upper (D 6) (R 6) [24,33,130,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18467 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 134 76 274 33 100 228 356), lower := (rows 25 35 134 76 274 33 64 128 256), losses := [] }

theorem u18467 : Upper (D 6) (R 6) [24,33,130,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18468 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 336, targets := 4 }], pairs := [(0,2),(3,1),(4,2)], upper := (rows 25 35 134 76 274 36 97 225 353), lower := (rows 25 35 134 76 274 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 16 44 67 131 259), good := (rows 505 481 492 108 464 44 64 128 256) },{ target := 2, region := (rows 9 2 0 8 22 32 66 130 258), good := (rows 25 499 466 89 466 48 64 128 256) }] }

theorem u18468 : Upper (D 6) (R 6) [24,33,130,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18469 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 404, targets := 64 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 25 35 134 76 274 96 101 165 293), lower := (rows 25 35 134 76 274 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 104 64 128 256), good := (rows 59 35 130 104 274 96 96 128 256) }] }

theorem u18469 : Upper (D 6) (R 6) [24,33,130,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18470 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 134 76 276 33 98 226 354), lower := (rows 25 35 134 76 276 33 64 128 256), losses := [] }

theorem u18470 : Upper (D 6) (R 6) [24,33,130,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18471 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 34, targets := 4 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,1),(1,2),(1,6)], upper := (rows 25 35 134 76 276 34 97 225 353), lower := (rows 25 35 134 76 276 34 64 128 256), losses := [{ target := 1, region := (rows 29 0 4 12 20 32 66 130 258), good := (rows 25 481 477 93 285 480 64 128 256) }] }

theorem u18471 : Upper (D 6) (R 6) [24,33,130,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18472 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 25 35 134 76 276 96 99 163 291), lower := (rows 25 35 134 76 276 96 64 128 256), losses := [] }

theorem u18472 : Upper (D 6) (R 6) [24,33,130,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18473 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 134 76 304 33 70 198 326), lower := (rows 25 35 134 76 304 33 64 128 256), losses := [] }

theorem u18473 : Upper (D 6) (R 6) [24,33,130,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18474 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 134 76 304 34 69 197 325), lower := (rows 25 35 134 76 304 34 64 128 256), losses := [] }

theorem u18474 : Upper (D 6) (R 6) [24,33,130,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18475 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 1, region := 336, targets := 4 }], pairs := [(2,5),(3,5),(4,2)], upper := (rows 25 35 134 76 304 36 67 195 323), lower := (rows 25 35 134 76 304 36 64 128 256), losses := [] }

theorem u18475 : Upper (D 6) (R 6) [24,33,130,68,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18476 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 25 35 134 76 304 96 71 135 263), lower := (rows 25 35 134 76 304 96 64 128 256), losses := [] }

theorem u18476 : Upper (D 6) (R 6) [24,33,130,68,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18477 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 134 76 336 33 102 166 294), lower := (rows 25 35 134 76 336 33 64 128 256), losses := [] }

theorem u18477 : Upper (D 6) (R 6) [24,33,130,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18478 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(1,6),(2,6)], upper := (rows 25 35 134 76 336 34 101 165 293), lower := (rows 25 35 134 76 336 34 64 128 256), losses := [] }

theorem u18478 : Upper (D 6) (R 6) [24,33,130,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18479 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 1, region := 336, targets := 4 }], pairs := [(1,6),(2,6),(4,2)], upper := (rows 25 35 134 76 336 36 99 163 291), lower := (rows 25 35 134 76 336 36 64 128 256), losses := [] }

theorem u18479 : Upper (D 6) (R 6) [24,33,130,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18479
end Delivery.IrregularNine14.P06
