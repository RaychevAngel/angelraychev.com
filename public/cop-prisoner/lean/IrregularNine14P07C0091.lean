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

def b5460 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 144, targets := 2 }], pairs := [(1,0),(1,5),(1,7),(4,1)], upper := (rows 35 70 268 104 145 160 66 145 273), lower := (rows 35 70 268 104 145 160 66 128 256), losses := [] }

theorem u5460 : Upper (D 7) (R 7) [34,68,264,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5461 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 268 104 145 160 80 131 259), lower := (rows 35 70 268 104 145 160 80 128 256), losses := [] }

theorem u5461 : Upper (D 7) (R 7) [34,68,264,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5461 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5462 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(3,7),(4,6)], upper := (rows 35 70 268 104 146 160 65 145 273), lower := (rows 35 70 268 104 146 160 65 128 256), losses := [] }

theorem u5462 : Upper (D 7) (R 7) [34,68,264,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5463 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 268 104 146 160 80 129 257), lower := (rows 35 70 268 104 146 160 80 128 256), losses := [] }

theorem u5463 : Upper (D 7) (R 7) [34,68,264,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5463 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5464 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 35 70 268 137 81 160 66 176 304), lower := (rows 35 70 268 137 81 160 66 128 256), losses := [] }

theorem u5464 : Upper (D 7) (R 7) [34,68,264,129,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5465 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 268 137 81 160 80 162 290), lower := (rows 35 70 268 137 81 160 80 128 256), losses := [] }

theorem u5465 : Upper (D 7) (R 7) [34,68,264,129,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5465 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5466 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 268 137 81 160 96 146 274), lower := (rows 35 70 268 137 81 160 96 128 256), losses := [] }

theorem u5466 : Upper (D 7) (R 7) [34,68,264,129,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5467 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 80, targets := 128 },{ cop := 1, region := 176, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 35 70 268 137 112 160 65 146 274), lower := (rows 35 70 268 137 112 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 82 235 64 131 259), good := (rows 434 502 300 428 112 160 496 160 256) }] }

theorem u5467 : Upper (D 7) (R 7) [34,68,264,129,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5468 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 35 70 268 137 112 160 66 145 273), lower := (rows 35 70 268 137 112 160 66 128 256), losses := [] }

theorem u5468 : Upper (D 7) (R 7) [34,68,264,129,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5469 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 268 137 112 160 80 131 259), lower := (rows 35 70 268 137 112 160 80 128 256), losses := [] }

theorem u5469 : Upper (D 7) (R 7) [34,68,264,129,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5469 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5470 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 6, region := 16, targets := 32 }], pairs := [(1,0),(2,0),(3,0),(4,5)], upper := (rows 35 70 268 138 81 160 65 176 304), lower := (rows 35 70 268 138 81 160 65 128 256), losses := [] }

theorem u5470 : Upper (D 7) (R 7) [34,68,264,130,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5471 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 268 138 81 160 80 161 289), lower := (rows 35 70 268 138 81 160 80 128 256), losses := [] }

theorem u5471 : Upper (D 7) (R 7) [34,68,264,130,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5471 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5472 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 268 138 81 160 96 145 273), lower := (rows 35 70 268 138 81 160 96 128 256), losses := [] }

theorem u5472 : Upper (D 7) (R 7) [34,68,264,130,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5473 : Route 9 := (fun mask => (mask,id))

def c5473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5473 : Upper (D 7) (R 7) [34,68,264,130,96,128,1] 13 := by
  apply FastRouting.sound _ _ [34,68,264,130,96,128,1] 13 (by decide) (choices 1) [1,16] r5473 c5473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u412
  · exact u413

def b5474 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 268 138 112 160 80 129 257), lower := (rows 35 70 268 138 112 160 80 128 256), losses := [] }

theorem u5474 : Upper (D 7) (R 7) [34,68,264,130,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5474 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5475 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 70 268 138 208 33 65 176 304), lower := (rows 35 70 268 138 208 33 65 128 256), losses := [] }

theorem u5475 : Upper (D 7) (R 7) [34,68,264,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5476 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 268 138 208 33 80 161 289), lower := (rows 35 70 268 138 208 33 80 128 256), losses := [] }

theorem u5476 : Upper (D 7) (R 7) [34,68,264,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5476 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5477 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 70 268 138 208 33 96 145 273), lower := (rows 35 70 268 138 208 33 96 128 256), losses := [] }

theorem u5477 : Upper (D 7) (R 7) [34,68,264,130,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5478 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 268 152 112 33 65 130 386), lower := (rows 35 70 268 152 112 33 65 128 256), losses := [] }

theorem u5478 : Upper (D 7) (R 7) [34,68,264,144,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5479 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 35 70 268 152 112 33 66 129 385), lower := (rows 35 70 268 152 112 33 66 128 256), losses := [] }

theorem u5479 : Upper (D 7) (R 7) [34,68,264,144,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5480 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(4,7)], upper := (rows 35 70 268 152 112 33 192 131 259), lower := (rows 35 70 268 152 112 33 192 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 200 128 256), good := (rows 34 70 334 216 112 32 192 192 256) }] }

theorem u5480 : Upper (D 7) (R 7) [34,68,264,144,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5481 : Route 9 := (fun mask => (mask,id))

def c5481 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5481 : Upper (D 7) (R 7) [34,68,264,144,96,128,1] 13 := by
  apply FastRouting.sound _ _ [34,68,264,144,96,128,1] 13 (by decide) (choices 1) [1,2] r5481 c5481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u414
  · exact u415

def b5482 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 35 70 268 152 112 160 66 129 257), lower := (rows 35 70 268 152 112 160 66 128 256), losses := [] }

theorem u5482 : Upper (D 7) (R 7) [34,68,264,144,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5483 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 144, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,5)], upper := (rows 35 70 268 168 208 33 65 146 274), lower := (rows 35 70 268 168 208 33 65 128 256), losses := [] }

theorem u5483 : Upper (D 7) (R 7) [34,68,264,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5484 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 70 268 168 208 33 66 145 273), lower := (rows 35 70 268 168 208 33 66 128 256), losses := [] }

theorem u5484 : Upper (D 7) (R 7) [34,68,264,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5485 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 268 168 208 33 80 131 259), lower := (rows 35 70 268 168 208 33 80 128 256), losses := [] }

theorem u5485 : Upper (D 7) (R 7) [34,68,264,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5485 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5486 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 35 70 268 200 145 33 66 176 304), lower := (rows 35 70 268 200 145 33 66 128 256), losses := [] }

theorem u5486 : Upper (D 7) (R 7) [34,68,264,192,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5487 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 268 200 145 33 80 162 290), lower := (rows 35 70 268 200 145 33 80 128 256), losses := [] }

theorem u5487 : Upper (D 7) (R 7) [34,68,264,192,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5487 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5488 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 70 268 200 145 33 96 146 274), lower := (rows 35 70 268 200 145 33 96 128 256), losses := [] }

theorem u5488 : Upper (D 7) (R 7) [34,68,264,192,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5489 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 4, region := 72, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 70 268 200 145 48 65 162 290), lower := (rows 35 70 268 200 145 48 65 128 256), losses := [] }

theorem u5489 : Upper (D 7) (R 7) [34,68,264,192,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5489 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5490 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 268 200 145 48 66 161 289), lower := (rows 35 70 268 200 145 48 66 128 256), losses := [] }

theorem u5490 : Upper (D 7) (R 7) [34,68,264,192,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5490 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5491 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 4, region := 104, targets := 1 }], pairs := [(0,6),(3,0),(4,6)], upper := (rows 35 70 268 200 145 48 96 131 259), lower := (rows 35 70 268 200 145 48 96 128 256), losses := [] }

theorem u5491 : Upper (D 7) (R 7) [34,68,264,192,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5491 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5492 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 70 268 200 146 33 65 176 304), lower := (rows 35 70 268 200 146 33 65 128 256), losses := [] }

theorem u5492 : Upper (D 7) (R 7) [34,68,264,192,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5493 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 268 200 146 33 80 161 289), lower := (rows 35 70 268 200 146 33 80 128 256), losses := [] }

theorem u5493 : Upper (D 7) (R 7) [34,68,264,192,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5493 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5494 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 70 268 200 146 33 96 145 273), lower := (rows 35 70 268 200 146 33 96 128 256), losses := [] }

theorem u5494 : Upper (D 7) (R 7) [34,68,264,192,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5495 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 70 268 200 176 33 65 146 274), lower := (rows 35 70 268 200 176 33 65 128 256), losses := [] }

theorem u5495 : Upper (D 7) (R 7) [34,68,264,192,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5496 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 35 70 268 200 176 33 66 145 273), lower := (rows 35 70 268 200 176 33 66 128 256), losses := [] }

theorem u5496 : Upper (D 7) (R 7) [34,68,264,192,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5497 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 268 200 176 33 80 131 259), lower := (rows 35 70 268 200 176 33 80 128 256), losses := [] }

theorem u5497 : Upper (D 7) (R 7) [34,68,264,192,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5497 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5498 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 292 25 208 160 65 138 266), lower := (rows 35 70 292 25 208 160 65 128 256), losses := [] }

theorem u5498 : Upper (D 7) (R 7) [34,68,288,17,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5499 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(3,5),(4,5)], upper := (rows 35 70 292 25 208 160 66 137 265), lower := (rows 35 70 292 25 208 160 66 128 256), losses := [] }

theorem u5499 : Upper (D 7) (R 7) [34,68,288,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5500 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 70 292 25 208 160 72 131 259), lower := (rows 35 70 292 25 208 160 72 128 256), losses := [] }

theorem u5500 : Upper (D 7) (R 7) [34,68,288,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5500 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5501 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 292 26 145 160 65 200 328), lower := (rows 35 70 292 26 145 160 65 128 256), losses := [] }

theorem u5501 : Upper (D 7) (R 7) [34,68,288,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5502 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 70 292 26 145 160 72 193 321), lower := (rows 35 70 292 26 145 160 72 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 16 176 0 128 256), good := (rows 35 6 292 59 177 160 9 160 256) }] }

theorem u5502 : Upper (D 7) (R 7) [34,68,288,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5502 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5503 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 70 292 73 145 48 66 136 392), lower := (rows 35 70 292 73 145 48 66 128 256), losses := [] }

theorem u5503 : Upper (D 7) (R 7) [34,68,288,65,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5503 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5504 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 292 73 145 48 72 130 386), lower := (rows 35 70 292 73 145 48 72 128 256), losses := [] }

theorem u5504 : Upper (D 7) (R 7) [34,68,288,65,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5504 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5505 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 72, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 35 70 292 73 145 48 192 138 266), lower := (rows 35 70 292 73 145 48 192 128 256), losses := [] }

theorem u5505 : Upper (D 7) (R 7) [34,68,288,65,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5505 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5506 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 35 70 292 73 145 160 66 152 280), lower := (rows 35 70 292 73 145 160 66 128 256), losses := [] }

theorem u5506 : Upper (D 7) (R 7) [34,68,288,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5507 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 292 73 145 160 72 146 274), lower := (rows 35 70 292 73 145 160 72 128 256), losses := [] }

theorem u5507 : Upper (D 7) (R 7) [34,68,288,65,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5507 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5508 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 35 70 292 73 145 160 80 138 266), lower := (rows 35 70 292 73 145 160 80 128 256), losses := [] }

theorem u5508 : Upper (D 7) (R 7) [34,68,288,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5508 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5509 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 3, region := 438, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 35 70 292 73 146 160 65 152 280), lower := (rows 35 70 292 73 146 160 65 128 256), losses := [] }

theorem u5509 : Upper (D 7) (R 7) [34,68,288,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5510 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 292 73 146 160 72 145 273), lower := (rows 35 70 292 73 146 160 72 128 256), losses := [] }

theorem u5510 : Upper (D 7) (R 7) [34,68,288,65,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5510 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5511 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 420, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 35 70 292 73 146 160 80 137 265), lower := (rows 35 70 292 73 146 160 80 128 256), losses := [] }

theorem u5511 : Upper (D 7) (R 7) [34,68,288,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5511 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5512 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 3, region := 438, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 35 70 292 73 152 160 65 146 274), lower := (rows 35 70 292 73 152 160 65 128 256), losses := [] }

theorem u5512 : Upper (D 7) (R 7) [34,68,288,65,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5513 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 35 70 292 73 152 160 66 145 273), lower := (rows 35 70 292 73 152 160 66 128 256), losses := [] }

theorem u5513 : Upper (D 7) (R 7) [34,68,288,65,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5514 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 70 292 73 152 160 80 131 259), lower := (rows 35 70 292 73 152 160 80 128 256), losses := [] }

theorem u5514 : Upper (D 7) (R 7) [34,68,288,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5514 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5515 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 292 88 145 160 65 138 266), lower := (rows 35 70 292 88 145 160 65 128 256), losses := [] }

theorem u5515 : Upper (D 7) (R 7) [34,68,288,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5516 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(3,5),(4,5)], upper := (rows 35 70 292 88 145 160 66 137 265), lower := (rows 35 70 292 88 145 160 66 128 256), losses := [] }

theorem u5516 : Upper (D 7) (R 7) [34,68,288,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5517 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 292 88 145 160 72 131 259), lower := (rows 35 70 292 88 145 160 72 128 256), losses := [] }

theorem u5517 : Upper (D 7) (R 7) [34,68,288,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5517 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5518 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 292 137 208 40 65 146 274), lower := (rows 35 70 292 137 208 40 65 128 256), losses := [] }

theorem u5518 : Upper (D 7) (R 7) [34,68,288,129,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5518 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5519 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 35 70 292 137 208 40 66 145 273), lower := (rows 35 70 292 137 208 40 66 128 256), losses := [] }

theorem u5519 : Upper (D 7) (R 7) [34,68,288,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5519 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5519
end Delivery.IrregularNine14.P07
