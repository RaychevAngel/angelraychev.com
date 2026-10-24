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

def b5520 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 405, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 25 38 134 74 276 96 96 129 257), lower := (rows 25 38 134 74 276 96 96 128 256), losses := [] }

theorem u5520 : Upper (D 6) (R 6) [24,36,130,66,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5521 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 132, targets := 33 }], pairs := [(0,1),(2,0),(2,5)], upper := (rows 25 38 134 74 304 33 65 196 324), lower := (rows 25 38 134 74 304 33 65 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 26 105 105 130 258), good := (rows 121 500 404 505 368 97 97 128 256) }] }

theorem u5521 : Upper (D 6) (R 6) [24,36,130,66,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5522 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 305, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 74 304 33 68 193 321), lower := (rows 25 38 134 74 304 33 68 128 256), losses := [] }

theorem u5522 : Upper (D 6) (R 6) [24,36,130,66,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5523 : PairBound 9 := { available := 5, camps := [], pairs := [(1,6),(2,6),(4,6)], upper := (rows 25 38 134 74 304 96 65 133 261), lower := (rows 25 38 134 74 304 96 65 128 256), losses := [{ target := 6, region := (rows 1 50 45 8 48 32 0 193 321), good := (rows 415 54 134 398 310 438 389 128 256) }] }

theorem u5523 : Upper (D 6) (R 6) [24,36,130,66,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5524 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 305, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 74 304 96 68 129 257), lower := (rows 25 38 134 74 304 96 68 128 256), losses := [] }

theorem u5524 : Upper (D 6) (R 6) [24,36,130,66,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5525 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 74 336 33 65 164 292), lower := (rows 25 38 134 74 336 33 65 128 256), losses := [] }

theorem u5525 : Upper (D 6) (R 6) [24,36,130,66,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5526 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 305, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 74 336 33 68 161 289), lower := (rows 25 38 134 74 336 33 68 128 256), losses := [] }

theorem u5526 : Upper (D 6) (R 6) [24,36,130,66,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5527 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 38 134 74 336 33 96 133 261), lower := (rows 25 38 134 74 336 33 96 128 256), losses := [] }

theorem u5527 : Upper (D 6) (R 6) [24,36,130,66,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5528 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 142, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 38 134 76 273 96 65 162 290), lower := (rows 25 38 134 76 273 96 65 128 256), losses := [] }

theorem u5528 : Upper (D 6) (R 6) [24,36,130,68,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5529 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 305, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 76 273 96 66 161 289), lower := (rows 25 38 134 76 273 96 66 128 256), losses := [] }

theorem u5529 : Upper (D 6) (R 6) [24,36,130,68,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5530 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 110, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 38 134 76 273 96 96 131 259), lower := (rows 25 38 134 76 273 96 96 128 256), losses := [] }

theorem u5530 : Upper (D 6) (R 6) [24,36,130,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5531 : Route 9 := (fun mask => (mask,id))

def c5531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5531 : Upper (D 6) (R 6) [24,36,130,68,258,64,1] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,258,64,1] 13 (by decide) (choices 1) [1,32] r5531 c5531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u411
  · exact u412

def b5532 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 110, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 38 134 76 274 96 96 129 257), lower := (rows 25 38 134 76 274 96 96 128 256), losses := [] }

theorem u5532 : Upper (D 6) (R 6) [24,36,130,68,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5533 : PairBound 9 := { available := 66, camps := [], pairs := [(2,5),(3,1),(4,2)], upper := (rows 25 38 134 76 304 33 65 194 322), lower := (rows 25 38 134 76 304 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 16 97 97 128 256), good := (rows 121 108 140 108 368 97 97 128 256) },{ target := 2, region := (rows 1 2 0 8 18 97 97 130 258), good := (rows 121 498 402 104 368 97 97 128 256) },{ target := 5, region := (rows 1 2 6 10 16 0 97 130 258), good := (rows 89 462 398 76 336 65 65 128 256) }] }

theorem u5533 : Upper (D 6) (R 6) [24,36,130,68,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5534 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 305, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 76 304 33 66 193 321), lower := (rows 25 38 134 76 304 33 66 128 256), losses := [] }

theorem u5534 : Upper (D 6) (R 6) [24,36,130,68,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5535 : Route 9 := (fun mask => (mask,id))

def c5535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5535 : Upper (D 6) (R 6) [24,36,130,68,288,64,1] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,288,64,1] 13 (by decide) (choices 1) [1,2] r5535 c5535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u413
  · exact u414

def b5536 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 305, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 76 304 96 66 129 257), lower := (rows 25 38 134 76 304 96 66 128 256), losses := [] }

theorem u5536 : Upper (D 6) (R 6) [24,36,130,68,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5537 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 76 336 33 65 162 290), lower := (rows 25 38 134 76 336 33 65 128 256), losses := [] }

theorem u5537 : Upper (D 6) (R 6) [24,36,130,68,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5538 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 305, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 76 336 33 66 161 289), lower := (rows 25 38 134 76 336 33 66 128 256), losses := [] }

theorem u5538 : Upper (D 6) (R 6) [24,36,130,68,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5539 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 1, region := 72, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 25 38 134 76 336 33 96 131 259), lower := (rows 25 38 134 76 336 33 96 128 256), losses := [] }

theorem u5539 : Upper (D 6) (R 6) [24,36,130,68,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5540 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 134 104 274 33 65 196 324), lower := (rows 25 38 134 104 274 33 65 128 256), losses := [] }

theorem u5540 : Upper (D 6) (R 6) [24,36,130,96,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5541 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 72, targets := 1 },{ cop := 1, region := 72, targets := 2 }], pairs := [(0,1),(3,0),(3,1)], upper := (rows 25 38 134 104 274 33 68 193 321), lower := (rows 25 38 134 104 274 33 68 128 256), losses := [{ target := 1, region := (rows 17 0 4 26 16 49 70 144 272), good := (rows 441 108 204 104 505 33 68 128 256) }] }

theorem u5541 : Upper (D 6) (R 6) [24,36,130,96,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5542 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 134 104 276 33 65 194 322), lower := (rows 25 38 134 104 276 33 65 128 256), losses := [] }

theorem u5542 : Upper (D 6) (R 6) [24,36,130,96,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5543 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 72, targets := 5 }], pairs := [(0,2),(3,0),(3,2)], upper := (rows 25 38 134 104 276 33 66 193 321), lower := (rows 25 38 134 104 276 33 66 128 256), losses := [{ target := 2, region := (rows 17 2 0 26 16 49 70 144 272), good := (rows 441 106 202 104 505 33 74 128 256) }] }

theorem u5543 : Upper (D 6) (R 6) [24,36,130,96,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5544 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 25 38 196 11 112 288 65 134 262), lower := (rows 25 38 196 11 112 288 65 128 256), losses := [] }

theorem u5544 : Upper (D 6) (R 6) [24,36,192,3,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5544 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5545 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 25 38 196 11 112 288 66 133 261), lower := (rows 25 38 196 11 112 288 66 128 256), losses := [] }

theorem u5545 : Upper (D 6) (R 6) [24,36,192,3,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5545 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5546 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 25 38 196 11 112 288 68 131 259), lower := (rows 25 38 196 11 112 288 68 128 256), losses := [] }

theorem u5546 : Upper (D 6) (R 6) [24,36,192,3,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5546 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5547 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 11 336 34 65 164 292), lower := (rows 25 38 196 11 336 34 65 128 256), losses := [] }

theorem u5547 : Upper (D 6) (R 6) [24,36,192,3,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5548 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 7, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 38 196 11 336 34 68 161 289), lower := (rows 25 38 196 11 336 34 68 128 256), losses := [] }

theorem u5548 : Upper (D 6) (R 6) [24,36,192,3,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5549 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 196 11 336 34 96 133 261), lower := (rows 25 38 196 11 336 34 96 128 256), losses := [] }

theorem u5549 : Upper (D 6) (R 6) [24,36,192,3,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5550 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 25 38 196 13 82 288 65 162 290), lower := (rows 25 38 196 13 82 288 65 128 256), losses := [] }

theorem u5550 : Upper (D 6) (R 6) [24,36,192,5,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5550 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5551 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 25 38 196 13 82 288 66 161 289), lower := (rows 25 38 196 13 82 288 66 128 256), losses := [] }

theorem u5551 : Upper (D 6) (R 6) [24,36,192,5,66,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5551 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5552 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 25 38 196 13 82 288 96 131 259), lower := (rows 25 38 196 13 82 288 96 128 256), losses := [] }

theorem u5552 : Upper (D 6) (R 6) [24,36,192,5,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5552 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5553 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 89, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 25 38 196 13 112 288 65 130 258), lower := (rows 25 38 196 13 112 288 65 128 256), losses := [] }

theorem u5553 : Upper (D 6) (R 6) [24,36,192,5,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5553 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5554 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 25 38 196 13 112 288 66 131 259), lower := (rows 25 38 196 13 112 288 66 128 256), losses := [] }

theorem u5554 : Upper (D 6) (R 6) [24,36,192,5,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5554 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5555 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 13 274 34 65 224 352), lower := (rows 25 38 196 13 274 34 65 128 256), losses := [] }

theorem u5555 : Upper (D 6) (R 6) [24,36,192,5,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5556 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 196 13 274 34 96 193 321), lower := (rows 25 38 196 13 274 34 96 128 256), losses := [] }

theorem u5556 : Upper (D 6) (R 6) [24,36,192,5,258,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5557 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 13 304 34 65 194 322), lower := (rows 25 38 196 13 304 34 65 128 256), losses := [] }

theorem u5557 : Upper (D 6) (R 6) [24,36,192,5,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5558 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 196 13 304 34 66 193 321), lower := (rows 25 38 196 13 304 34 66 128 256), losses := [] }

theorem u5558 : Upper (D 6) (R 6) [24,36,192,5,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5559 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 13 336 34 65 162 290), lower := (rows 25 38 196 13 336 34 65 128 256), losses := [] }

theorem u5559 : Upper (D 6) (R 6) [24,36,192,5,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5560 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 196 13 336 34 66 161 289), lower := (rows 25 38 196 13 336 34 66 128 256), losses := [] }

theorem u5560 : Upper (D 6) (R 6) [24,36,192,5,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5561 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 196 13 336 34 96 131 259), lower := (rows 25 38 196 13 336 34 96 128 256), losses := [] }

theorem u5561 : Upper (D 6) (R 6) [24,36,192,5,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5562 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 25 38 196 41 82 288 65 134 262), lower := (rows 25 38 196 41 82 288 65 128 256), losses := [] }

theorem u5562 : Upper (D 6) (R 6) [24,36,192,33,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5562 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5563 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 25 38 196 41 82 288 66 133 261), lower := (rows 25 38 196 41 82 288 66 128 256), losses := [] }

theorem u5563 : Upper (D 6) (R 6) [24,36,192,33,66,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5563 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5564 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 297, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 25 38 196 41 82 288 68 131 259), lower := (rows 25 38 196 41 82 288 68 128 256), losses := [] }

theorem u5564 : Upper (D 6) (R 6) [24,36,192,33,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5564 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5565 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 41 336 34 65 134 262), lower := (rows 25 38 196 41 336 34 65 128 256), losses := [] }

theorem u5565 : Upper (D 6) (R 6) [24,36,192,33,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5566 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 196 41 336 34 66 133 261), lower := (rows 25 38 196 41 336 34 66 128 256), losses := [] }

theorem u5566 : Upper (D 6) (R 6) [24,36,192,33,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5567 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 7, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 38 196 41 336 34 68 131 259), lower := (rows 25 38 196 41 336 34 68 128 256), losses := [] }

theorem u5567 : Upper (D 6) (R 6) [24,36,192,33,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5568 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 25 38 196 73 274 34 65 164 292), lower := (rows 25 38 196 73 274 34 65 128 256), losses := [] }

theorem u5568 : Upper (D 6) (R 6) [24,36,192,65,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5569 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 7, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 38 196 73 274 34 68 161 289), lower := (rows 25 38 196 73 274 34 68 128 256), losses := [] }

theorem u5569 : Upper (D 6) (R 6) [24,36,192,65,258,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5570 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 132, targets := 34 },{ cop := 4, region := 105, targets := 4 }], pairs := [(0,2),(2,1),(2,5)], upper := (rows 25 38 196 73 274 34 96 133 261), lower := (rows 25 38 196 73 274 34 96 128 256), losses := [] }

theorem u5570 : Upper (D 6) (R 6) [24,36,192,65,258,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5571 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 73, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 196 73 276 34 65 162 290), lower := (rows 25 38 196 73 276 34 65 128 256), losses := [] }

theorem u5571 : Upper (D 6) (R 6) [24,36,192,65,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5572 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 196 73 276 34 66 161 289), lower := (rows 25 38 196 73 276 34 66 128 256), losses := [] }

theorem u5572 : Upper (D 6) (R 6) [24,36,192,65,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5573 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 196 73 276 34 96 131 259), lower := (rows 25 38 196 73 276 34 96 128 256), losses := [] }

theorem u5573 : Upper (D 6) (R 6) [24,36,192,65,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5574 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 73, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 196 73 304 34 65 134 262), lower := (rows 25 38 196 73 304 34 65 128 256), losses := [] }

theorem u5574 : Upper (D 6) (R 6) [24,36,192,65,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5575 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 132, targets := 34 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 38 196 73 304 34 66 133 261), lower := (rows 25 38 196 73 304 34 66 128 256), losses := [] }

theorem u5575 : Upper (D 6) (R 6) [24,36,192,65,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5576 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 7, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 38 196 73 304 34 68 131 259), lower := (rows 25 38 196 73 304 34 68 128 256), losses := [] }

theorem u5576 : Upper (D 6) (R 6) [24,36,192,65,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5577 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 4, region := 73, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 25 38 196 74 274 33 65 164 292), lower := (rows 25 38 196 74 274 33 65 128 256), losses := [] }

theorem u5577 : Upper (D 6) (R 6) [24,36,192,66,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5578 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 25 38 196 74 274 33 68 161 289), lower := (rows 25 38 196 74 274 33 68 128 256), losses := [] }

theorem u5578 : Upper (D 6) (R 6) [24,36,192,66,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5579 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 38 196 74 274 33 96 133 261), lower := (rows 25 38 196 74 274 33 96 128 256), losses := [] }

theorem u5579 : Upper (D 6) (R 6) [24,36,192,66,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5579
end Delivery.IrregularNine14.P06
