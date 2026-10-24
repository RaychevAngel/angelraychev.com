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

def b5460 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 2, region := 72, targets := 2 }], pairs := [(1,0),(1,6),(3,1)], upper := (rows 25 38 133 76 274 34 65 224 352), lower := (rows 25 38 133 76 274 34 65 128 256), losses := [] }

theorem u5460 : Upper (D 6) (R 6) [24,36,129,68,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5461 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 1, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1)], upper := (rows 25 38 133 76 274 34 96 193 321), lower := (rows 25 38 133 76 274 34 96 128 256), losses := [] }

theorem u5461 : Upper (D 6) (R 6) [24,36,129,68,258,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5462 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 38 133 76 274 96 65 162 290), lower := (rows 25 38 133 76 274 96 65 128 256), losses := [] }

theorem u5462 : Upper (D 6) (R 6) [24,36,129,68,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5463 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 1, region := 72, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 25 38 133 76 274 96 66 161 289), lower := (rows 25 38 133 76 274 96 66 128 256), losses := [] }

theorem u5463 : Upper (D 6) (R 6) [24,36,129,68,258,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5464 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 1, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1)], upper := (rows 25 38 133 76 274 96 96 131 259), lower := (rows 25 38 133 76 274 96 96 128 256), losses := [] }

theorem u5464 : Upper (D 6) (R 6) [24,36,129,68,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5465 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 2, region := 72, targets := 2 }], pairs := [(1,0),(1,6),(3,1)], upper := (rows 25 38 133 76 304 34 65 194 322), lower := (rows 25 38 133 76 304 34 65 128 256), losses := [] }

theorem u5465 : Upper (D 6) (R 6) [24,36,129,68,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5466 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 1, region := 72, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 25 38 133 76 304 34 66 193 321), lower := (rows 25 38 133 76 304 34 66 128 256), losses := [] }

theorem u5466 : Upper (D 6) (R 6) [24,36,129,68,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5467 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 38 133 76 304 96 65 130 258), lower := (rows 25 38 133 76 304 96 65 128 256), losses := [] }

theorem u5467 : Upper (D 6) (R 6) [24,36,129,68,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5468 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 1, region := 72, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 25 38 133 76 304 96 66 131 259), lower := (rows 25 38 133 76 304 96 66 128 256), losses := [] }

theorem u5468 : Upper (D 6) (R 6) [24,36,129,68,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5469 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 25 38 133 104 276 34 65 194 322), lower := (rows 25 38 133 104 276 34 65 128 256), losses := [{ target := 0, region := (rows 0 22 4 72 16 55 64 128 256), good := (rows 58 38 166 104 310 34 104 128 256) }] }

theorem u5469 : Upper (D 6) (R 6) [24,36,129,96,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5470 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 405, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 25 38 133 104 276 34 66 193 321), lower := (rows 25 38 133 104 276 34 66 128 256), losses := [] }

theorem u5470 : Upper (D 6) (R 6) [24,36,129,96,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5471 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 134 11 84 96 65 416 288), lower := (rows 25 38 134 11 84 96 65 128 256), losses := [] }

theorem u5471 : Upper (D 6) (R 6) [24,36,130,3,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5472 : PairBound 9 := { available := 257, camps := [{ cop := 7, region := 118, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 11 84 96 96 385 257), lower := (rows 25 38 134 11 84 96 96 128 256), losses := [] }

theorem u5472 : Upper (D 6) (R 6) [24,36,130,3,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5473 : Route 9 := (fun mask => (mask,id))

def c5473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5473 : Upper (D 6) (R 6) [24,36,130,3,68,64,256] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,68,64,256] 13 (by decide) (choices 1) [1,32] r5473 c5473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u401
  · exact u402

def b5474 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 25 38 134 11 84 288 65 224 352), lower := (rows 25 38 134 11 84 288 65 128 256), losses := [] }

theorem u5474 : Upper (D 6) (R 6) [24,36,130,3,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5474 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5475 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(4,0),(4,1)], upper := (rows 25 38 134 11 84 288 96 193 321), lower := (rows 25 38 134 11 84 288 96 128 256), losses := [] }

theorem u5475 : Upper (D 6) (R 6) [24,36,130,3,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5475 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5476 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 25 38 134 11 112 288 65 196 324), lower := (rows 25 38 134 11 112 288 65 128 256), losses := [] }

theorem u5476 : Upper (D 6) (R 6) [24,36,130,3,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5476 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5477 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(4,0),(4,1)], upper := (rows 25 38 134 11 112 288 68 193 321), lower := (rows 25 38 134 11 112 288 68 128 256), losses := [] }

theorem u5477 : Upper (D 6) (R 6) [24,36,130,3,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5477 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5478 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 11 276 96 65 224 352), lower := (rows 25 38 134 11 276 96 65 128 256), losses := [] }

theorem u5478 : Upper (D 6) (R 6) [24,36,130,3,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5479 : Route 9 := (fun mask => (mask,id))

def c5479 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5479 : Upper (D 6) (R 6) [24,36,130,3,260,64,32] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,260,64,32] 13 (by decide) (choices 1) [1,64] r5479 c5479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u403
  · exact u404

def b5480 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 11 304 96 65 196 324), lower := (rows 25 38 134 11 304 96 65 128 256), losses := [] }

theorem u5480 : Upper (D 6) (R 6) [24,36,130,3,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5481 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 3, region := 196, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 38 134 11 304 96 68 193 321), lower := (rows 25 38 134 11 304 96 68 128 256), losses := [] }

theorem u5481 : Upper (D 6) (R 6) [24,36,130,3,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5482 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 11 336 96 65 164 292), lower := (rows 25 38 134 11 336 96 65 128 256), losses := [] }

theorem u5482 : Upper (D 6) (R 6) [24,36,130,3,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5483 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 38 134 11 336 96 68 161 289), lower := (rows 25 38 134 11 336 96 68 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 126 70 137 265), good := (rows 441 100 228 505 368 96 100 128 256) }] }

theorem u5483 : Upper (D 6) (R 6) [24,36,130,3,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5484 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 25 38 134 11 336 96 96 133 261), lower := (rows 25 38 134 11 336 96 96 128 256), losses := [] }

theorem u5484 : Upper (D 6) (R 6) [24,36,130,3,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5485 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 134 13 82 96 65 416 288), lower := (rows 25 38 134 13 82 96 65 128 256), losses := [] }

theorem u5485 : Upper (D 6) (R 6) [24,36,130,5,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5486 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 25 38 134 13 82 96 96 385 257), lower := (rows 25 38 134 13 82 96 96 128 256), losses := [] }

theorem u5486 : Upper (D 6) (R 6) [24,36,130,5,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5487 : Route 9 := (fun mask => (mask,id))

def c5487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5487 : Upper (D 6) (R 6) [24,36,130,5,66,64,256] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,66,64,256] 13 (by decide) (choices 1) [1,32] r5487 c5487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u405
  · exact u406

def b5488 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 25 38 134 13 82 288 65 224 352), lower := (rows 25 38 134 13 82 288 65 128 256), losses := [] }

theorem u5488 : Upper (D 6) (R 6) [24,36,130,5,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5488 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5489 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 25 38 134 13 82 288 96 193 321), lower := (rows 25 38 134 13 82 288 96 128 256), losses := [] }

theorem u5489 : Upper (D 6) (R 6) [24,36,130,5,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5489 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5490 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 89, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 25 38 134 13 112 288 65 194 322), lower := (rows 25 38 134 13 112 288 65 128 256), losses := [] }

theorem u5490 : Upper (D 6) (R 6) [24,36,130,5,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5490 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5491 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 25 38 134 13 112 288 66 193 321), lower := (rows 25 38 134 13 112 288 66 128 256), losses := [] }

theorem u5491 : Upper (D 6) (R 6) [24,36,130,5,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5491 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5492 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 13 274 96 65 224 352), lower := (rows 25 38 134 13 274 96 65 128 256), losses := [] }

theorem u5492 : Upper (D 6) (R 6) [24,36,130,5,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5493 : Route 9 := (fun mask => (mask,id))

def c5493 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5493 : Upper (D 6) (R 6) [24,36,130,5,258,64,32] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,258,64,32] 13 (by decide) (choices 1) [1,64] r5493 c5493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u407
  · exact u408

def b5494 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 13 304 96 65 194 322), lower := (rows 25 38 134 13 304 96 65 128 256), losses := [] }

theorem u5494 : Upper (D 6) (R 6) [24,36,130,5,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5495 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 38 134 13 304 96 66 193 321), lower := (rows 25 38 134 13 304 96 66 128 256), losses := [{ target := 1, region := (rows 71 0 4 14 114 96 64 224 352), good := (rows 25 445 157 13 432 497 505 128 256) }] }

theorem u5495 : Upper (D 6) (R 6) [24,36,130,5,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5496 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 13 336 96 65 162 290), lower := (rows 25 38 134 13 336 96 65 128 256), losses := [] }

theorem u5496 : Upper (D 6) (R 6) [24,36,130,5,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5497 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 38 134 13 336 96 66 161 289), lower := (rows 25 38 134 13 336 96 66 128 256), losses := [{ target := 1, region := (rows 67 0 4 14 112 112 64 243 371), good := (rows 441 445 397 397 497 497 505 128 256) }] }

theorem u5497 : Upper (D 6) (R 6) [24,36,130,5,320,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5498 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 25 38 134 13 336 96 96 131 259), lower := (rows 25 38 134 13 336 96 96 128 256), losses := [] }

theorem u5498 : Upper (D 6) (R 6) [24,36,130,5,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5499 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 25 38 134 41 82 288 65 196 324), lower := (rows 25 38 134 41 82 288 65 128 256), losses := [] }

theorem u5499 : Upper (D 6) (R 6) [24,36,130,33,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5499 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5500 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 297, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 25 38 134 41 82 288 68 193 321), lower := (rows 25 38 134 41 82 288 68 128 256), losses := [] }

theorem u5500 : Upper (D 6) (R 6) [24,36,130,33,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5500 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5501 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 89, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 25 38 134 41 84 288 65 194 322), lower := (rows 25 38 134 41 84 288 65 128 256), losses := [] }

theorem u5501 : Upper (D 6) (R 6) [24,36,130,33,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5501 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5502 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 297, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 25 38 134 41 84 288 66 193 321), lower := (rows 25 38 134 41 84 288 66 128 256), losses := [] }

theorem u5502 : Upper (D 6) (R 6) [24,36,130,33,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5502 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5503 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 134 41 274 96 65 196 324), lower := (rows 25 38 134 41 274 96 65 128 256), losses := [] }

theorem u5503 : Upper (D 6) (R 6) [24,36,130,33,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5504 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 38 134 41 274 96 68 193 321), lower := (rows 25 38 134 41 274 96 68 128 256), losses := [{ target := 1, region := (rows 17 0 4 25 16 118 70 144 272), good := (rows 441 100 228 41 505 96 100 128 256) }] }

theorem u5504 : Upper (D 6) (R 6) [24,36,130,33,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5505 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 134 41 276 96 65 194 322), lower := (rows 25 38 134 41 276 96 65 128 256), losses := [] }

theorem u5505 : Upper (D 6) (R 6) [24,36,130,33,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5506 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 38 134 41 276 96 66 193 321), lower := (rows 25 38 134 41 276 96 66 128 256), losses := [{ target := 1, region := (rows 71 0 4 106 18 96 64 224 352), good := (rows 25 445 157 425 277 489 505 128 256) }] }

theorem u5506 : Upper (D 6) (R 6) [24,36,130,33,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5507 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 73 274 96 65 164 292), lower := (rows 25 38 134 73 274 96 65 128 256), losses := [] }

theorem u5507 : Upper (D 6) (R 6) [24,36,130,65,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5508 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 38 134 73 274 96 68 161 289), lower := (rows 25 38 134 73 274 96 68 128 256), losses := [{ target := 1, region := (rows 17 0 4 24 16 126 70 153 281), good := (rows 441 100 228 489 505 96 100 128 256) }] }

theorem u5508 : Upper (D 6) (R 6) [24,36,130,65,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5509 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 134 73 274 96 96 133 261), lower := (rows 25 38 134 73 274 96 96 128 256), losses := [] }

theorem u5509 : Upper (D 6) (R 6) [24,36,130,65,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5510 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 73 276 96 65 162 290), lower := (rows 25 38 134 73 276 96 65 128 256), losses := [] }

theorem u5510 : Upper (D 6) (R 6) [24,36,130,65,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5511 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 38 134 73 276 96 66 161 289), lower := (rows 25 38 134 73 276 96 66 128 256), losses := [{ target := 1, region := (rows 67 0 4 104 22 104 64 235 363), good := (rows 441 445 405 489 276 489 505 128 256) }] }

theorem u5511 : Upper (D 6) (R 6) [24,36,130,65,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5512 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 134 73 276 96 96 131 259), lower := (rows 25 38 134 73 276 96 96 128 256), losses := [] }

theorem u5512 : Upper (D 6) (R 6) [24,36,130,65,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5513 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 73 304 96 65 134 262), lower := (rows 25 38 134 73 304 96 65 128 256), losses := [] }

theorem u5513 : Upper (D 6) (R 6) [24,36,130,65,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5514 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 38 134 73 304 96 66 133 261), lower := (rows 25 38 134 73 304 96 66 128 256), losses := [{ target := 1, region := (rows 123 0 4 104 82 104 64 134 262), good := (rows 57 445 405 121 313 121 505 128 256) }] }

theorem u5514 : Upper (D 6) (R 6) [24,36,130,65,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5515 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 25 38 134 73 304 96 68 131 259), lower := (rows 25 38 134 73 304 96 68 128 256), losses := [{ target := 2, region := (rows 123 2 0 104 82 104 64 134 262), good := (rows 57 443 403 121 313 121 505 128 256) }] }

theorem u5515 : Upper (D 6) (R 6) [24,36,130,65,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5516 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 142, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 38 134 74 273 96 65 164 292), lower := (rows 25 38 134 74 273 96 65 128 256), losses := [] }

theorem u5516 : Upper (D 6) (R 6) [24,36,130,66,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5517 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 305, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 74 273 96 68 161 289), lower := (rows 25 38 134 74 273 96 68 128 256), losses := [] }

theorem u5517 : Upper (D 6) (R 6) [24,36,130,66,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5518 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 405, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 25 38 134 74 273 96 96 133 261), lower := (rows 25 38 134 74 273 96 96 128 256), losses := [] }

theorem u5518 : Upper (D 6) (R 6) [24,36,130,66,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5519 : Route 9 := (fun mask => (mask,id))

def c5519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5519 : Upper (D 6) (R 6) [24,36,130,66,260,64,1] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,260,64,1] 13 (by decide) (choices 1) [1,32] r5519 c5519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u409
  · exact u410

#print axioms u5519
end Delivery.IrregularNine14.P06
