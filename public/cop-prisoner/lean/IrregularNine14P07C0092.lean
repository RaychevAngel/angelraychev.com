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

def b5520 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 292 137 208 40 80 131 259), lower := (rows 35 70 292 137 208 40 80 128 256), losses := [] }

theorem u5520 : Upper (D 7) (R 7) [34,68,288,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5520 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5521 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 388 25 176 40 65 194 322), lower := (rows 35 70 388 25 176 40 65 128 256), losses := [] }

theorem u5521 : Upper (D 7) (R 7) [34,68,384,17,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5521 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5522 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 388 25 176 40 66 193 321), lower := (rows 35 70 388 25 176 40 66 128 256), losses := [] }

theorem u5522 : Upper (D 7) (R 7) [34,68,384,17,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5522 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5523 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 388 25 208 33 66 168 296), lower := (rows 35 70 388 25 208 33 66 128 256), losses := [] }

theorem u5523 : Upper (D 7) (R 7) [34,68,384,17,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5524 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 388, targets := 1 }], pairs := [(0,6),(2,0),(2,6)], upper := (rows 35 70 388 25 208 33 72 162 290), lower := (rows 35 70 388 25 208 33 72 128 256), losses := [] }

theorem u5524 : Upper (D 7) (R 7) [34,68,384,17,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5524 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5525 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 70 388 25 208 33 96 138 266), lower := (rows 35 70 388 25 208 33 96 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 24 32 97 136 264), good := (rows 98 70 388 478 208 96 96 128 256) }] }

theorem u5525 : Upper (D 7) (R 7) [34,68,384,17,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5526 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 388, targets := 1 },{ cop := 0, region := 388, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 35 70 388 25 208 40 65 162 290), lower := (rows 35 70 388 25 208 40 65 128 256), losses := [{ target := 0, region := (rows 0 82 109 8 80 40 64 137 265), good := (rows 422 86 388 446 214 428 470 128 256) }] }

theorem u5526 : Upper (D 7) (R 7) [34,68,384,17,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5526 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5527 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 388 25 208 40 66 161 289), lower := (rows 35 70 388 25 208 40 66 128 256), losses := [] }

theorem u5527 : Upper (D 7) (R 7) [34,68,384,17,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5527 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5528 : Route 9 := (fun mask => (mask,id))

def c5528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5528 : Upper (D 7) (R 7) [34,68,384,17,192,8,32] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,192,8,32] 13 (by decide) (choices 1) [1,2] r5528 c5528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u416
  · exact u417

def b5529 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,1)], upper := (rows 35 70 388 26 145 33 72 224 352), lower := (rows 35 70 388 26 145 33 72 128 256), losses := [{ target := 1, region := (rows 1 0 76 8 16 49 72 136 264), good := (rows 33 68 388 508 177 33 460 128 256) }] }

theorem u5529 : Upper (D 7) (R 7) [34,68,384,18,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5529 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5530 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 70 388 26 145 33 96 200 328), lower := (rows 35 70 388 26 145 33 96 128 256), losses := [{ target := 0, region := (rows 0 18 28 24 16 32 97 144 272), good := (rows 98 70 388 414 478 96 96 128 256) }] }

theorem u5530 : Upper (D 7) (R 7) [34,68,384,18,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5531 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 70 388 26 176 33 65 200 328), lower := (rows 35 70 388 26 176 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 79 73 17 32 64 194 322), good := (rows 446 462 388 414 176 60 478 128 256) }] }

theorem u5531 : Upper (D 7) (R 7) [34,68,384,18,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5532 : Route 9 := (fun mask => (mask,id))

def c5532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5532 : Upper (D 7) (R 7) [34,68,384,18,160,1,8] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,160,1,8] 13 (by decide) (choices 1) [1,64] r5532 c5532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u418
  · exact u419

def b5533 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 35 70 388 26 208 33 65 168 296), lower := (rows 35 70 388 26 208 33 65 128 256), losses := [] }

theorem u5533 : Upper (D 7) (R 7) [34,68,384,18,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5534 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 90, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 70 388 26 208 33 72 161 289), lower := (rows 35 70 388 26 208 33 72 128 256), losses := [] }

theorem u5534 : Upper (D 7) (R 7) [34,68,384,18,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5534 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5535 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 35 70 388 26 208 33 96 137 265), lower := (rows 35 70 388 26 208 33 96 128 256), losses := [] }

theorem u5535 : Upper (D 7) (R 7) [34,68,384,18,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5536 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 6, region := 16, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 35 70 388 56 81 160 65 138 266), lower := (rows 35 70 388 56 81 160 65 128 256), losses := [] }

theorem u5536 : Upper (D 7) (R 7) [34,68,384,48,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5537 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 35 70 388 56 81 160 66 137 265), lower := (rows 35 70 388 56 81 160 66 128 256), losses := [] }

theorem u5537 : Upper (D 7) (R 7) [34,68,384,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5538 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 88, targets := 2 },{ cop := 0, region := 88, targets := 128 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 70 388 56 81 160 72 131 259), lower := (rows 35 70 388 56 81 160 72 128 256), losses := [] }

theorem u5538 : Upper (D 7) (R 7) [34,68,384,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5538 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5539 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 70 388 56 208 33 65 138 266), lower := (rows 35 70 388 56 208 33 65 128 256), losses := [{ target := 0, region := (rows 0 82 127 9 82 32 64 201 329), good := (rows 446 470 388 446 470 428 478 128 256) }] }

theorem u5539 : Upper (D 7) (R 7) [34,68,384,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5540 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 388 56 208 33 66 137 265), lower := (rows 35 70 388 56 208 33 66 128 256), losses := [] }

theorem u5540 : Upper (D 7) (R 7) [34,68,384,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5541 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,6),(2,5),(2,6)], upper := (rows 35 70 388 56 208 33 72 131 259), lower := (rows 35 70 388 56 208 33 72 128 256), losses := [] }

theorem u5541 : Upper (D 7) (R 7) [34,68,384,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5541 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5542 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 70 388 73 145 48 66 168 296), lower := (rows 35 70 388 73 145 48 66 128 256), losses := [] }

theorem u5542 : Upper (D 7) (R 7) [34,68,384,65,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5542 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5543 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 388 73 145 48 72 162 290), lower := (rows 35 70 388 73 145 48 72 128 256), losses := [] }

theorem u5543 : Upper (D 7) (R 7) [34,68,384,65,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5543 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5544 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 388 73 145 48 96 138 266), lower := (rows 35 70 388 73 145 48 96 128 256), losses := [] }

theorem u5544 : Upper (D 7) (R 7) [34,68,384,65,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5544 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5545 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 388 73 146 33 72 176 304), lower := (rows 35 70 388 73 146 33 72 128 256), losses := [] }

theorem u5545 : Upper (D 7) (R 7) [34,68,384,65,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5545 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5546 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 388 73 146 33 80 168 296), lower := (rows 35 70 388 73 146 33 80 128 256), losses := [] }

theorem u5546 : Upper (D 7) (R 7) [34,68,384,65,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5546 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5547 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 73 146 33 96 152 280), lower := (rows 35 70 388 73 146 33 96 128 256), losses := [] }

theorem u5547 : Upper (D 7) (R 7) [34,68,384,65,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5548 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 35 70 388 73 152 33 66 176 304), lower := (rows 35 70 388 73 152 33 66 128 256), losses := [] }

theorem u5548 : Upper (D 7) (R 7) [34,68,384,65,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5549 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 70 388 73 152 33 80 162 290), lower := (rows 35 70 388 73 152 33 80 128 256), losses := [] }

theorem u5549 : Upper (D 7) (R 7) [34,68,384,65,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5549 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5550 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 73 152 33 96 146 274), lower := (rows 35 70 388 73 152 33 96 128 256), losses := [] }

theorem u5550 : Upper (D 7) (R 7) [34,68,384,65,136,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5551 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 35 70 388 73 176 33 66 152 280), lower := (rows 35 70 388 73 176 33 66 128 256), losses := [] }

theorem u5551 : Upper (D 7) (R 7) [34,68,384,65,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5552 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 388 73 176 33 72 146 274), lower := (rows 35 70 388 73 176 33 72 128 256), losses := [] }

theorem u5552 : Upper (D 7) (R 7) [34,68,384,65,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5552 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5553 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 388 73 176 33 80 138 266), lower := (rows 35 70 388 73 176 33 80 128 256), losses := [] }

theorem u5553 : Upper (D 7) (R 7) [34,68,384,65,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5553 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5554 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 70 388 88 145 33 66 168 296), lower := (rows 35 70 388 88 145 33 66 128 256), losses := [] }

theorem u5554 : Upper (D 7) (R 7) [34,68,384,80,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5555 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 388 88 145 33 72 162 290), lower := (rows 35 70 388 88 145 33 72 128 256), losses := [] }

theorem u5555 : Upper (D 7) (R 7) [34,68,384,80,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5555 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5556 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 88 145 33 96 138 266), lower := (rows 35 70 388 88 145 33 96 128 256), losses := [] }

theorem u5556 : Upper (D 7) (R 7) [34,68,384,80,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5557 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 88 176 33 65 138 266), lower := (rows 35 70 388 88 176 33 65 128 256), losses := [] }

theorem u5557 : Upper (D 7) (R 7) [34,68,384,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5558 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 70 388 88 176 33 66 137 265), lower := (rows 35 70 388 88 176 33 66 128 256), losses := [] }

theorem u5558 : Upper (D 7) (R 7) [34,68,384,80,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5559 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 70 388 88 176 33 72 131 259), lower := (rows 35 70 388 88 176 33 72 128 256), losses := [] }

theorem u5559 : Upper (D 7) (R 7) [34,68,384,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5559 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5560 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 107, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 35 70 388 104 145 33 66 152 280), lower := (rows 35 70 388 104 145 33 66 128 256), losses := [] }

theorem u5560 : Upper (D 7) (R 7) [34,68,384,96,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5561 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 388 104 145 33 72 146 274), lower := (rows 35 70 388 104 145 33 72 128 256), losses := [] }

theorem u5561 : Upper (D 7) (R 7) [34,68,384,96,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5561 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5562 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 388 104 145 33 80 138 266), lower := (rows 35 70 388 104 145 33 80 128 256), losses := [] }

theorem u5562 : Upper (D 7) (R 7) [34,68,384,96,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5562 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5563 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 388 104 145 48 65 138 266), lower := (rows 35 70 388 104 145 48 65 128 256), losses := [] }

theorem u5563 : Upper (D 7) (R 7) [34,68,384,96,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5563 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5564 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 388 104 145 48 66 137 265), lower := (rows 35 70 388 104 145 48 66 128 256), losses := [] }

theorem u5564 : Upper (D 7) (R 7) [34,68,384,96,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5564 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5565 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 388 104 145 48 72 131 259), lower := (rows 35 70 388 104 145 48 72 128 256), losses := [] }

theorem u5565 : Upper (D 7) (R 7) [34,68,384,96,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5565 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5566 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 104 146 33 65 152 280), lower := (rows 35 70 388 104 146 33 65 128 256), losses := [] }

theorem u5566 : Upper (D 7) (R 7) [34,68,384,96,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5567 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 388 104 146 33 72 145 273), lower := (rows 35 70 388 104 146 33 72 128 256), losses := [] }

theorem u5567 : Upper (D 7) (R 7) [34,68,384,96,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5567 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5568 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 388 104 146 33 80 137 265), lower := (rows 35 70 388 104 146 33 80 128 256), losses := [] }

theorem u5568 : Upper (D 7) (R 7) [34,68,384,96,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5568 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5569 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 104 152 33 65 146 274), lower := (rows 35 70 388 104 152 33 65 128 256), losses := [] }

theorem u5569 : Upper (D 7) (R 7) [34,68,384,96,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5570 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 107, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 35 70 388 104 152 33 66 145 273), lower := (rows 35 70 388 104 152 33 66 128 256), losses := [] }

theorem u5570 : Upper (D 7) (R 7) [34,68,384,96,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5571 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 70 388 104 152 33 80 131 259), lower := (rows 35 70 388 104 152 33 80 128 256), losses := [] }

theorem u5571 : Upper (D 7) (R 7) [34,68,384,96,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5571 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5572 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 92, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 194 13 28 112 288 65 130 386), lower := (rows 35 194 13 28 112 288 65 128 256), losses := [] }

theorem u5572 : Upper (D 7) (R 7) [34,192,9,20,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5572 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5573 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 194 13 28 112 288 66 129 385), lower := (rows 35 194 13 28 112 288 66 128 256), losses := [] }

theorem u5573 : Upper (D 7) (R 7) [34,192,9,20,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5573 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5574 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 28 112 288 192 131 259), lower := (rows 35 194 13 28 112 288 192 128 256), losses := [] }

theorem u5574 : Upper (D 7) (R 7) [34,192,9,20,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5574 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5575 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 13 56 336 36 65 130 386), lower := (rows 35 194 13 56 336 36 65 128 256), losses := [] }

theorem u5575 : Upper (D 7) (R 7) [34,192,9,48,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5575 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5576 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 35 194 13 56 336 36 66 129 385), lower := (rows 35 194 13 56 336 36 66 128 256), losses := [] }

theorem u5576 : Upper (D 7) (R 7) [34,192,9,48,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5576 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5577 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 56 336 36 192 131 259), lower := (rows 35 194 13 56 336 36 192 128 256), losses := [] }

theorem u5577 : Upper (D 7) (R 7) [34,192,9,48,320,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5577 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5578 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 35 194 13 76 176 288 65 146 274), lower := (rows 35 194 13 76 176 288 65 128 256), losses := [] }

theorem u5578 : Upper (D 7) (R 7) [34,192,9,68,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5578 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5579 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 194 13 76 176 288 66 145 273), lower := (rows 35 194 13 76 176 288 66 128 256), losses := [] }

theorem u5579 : Upper (D 7) (R 7) [34,192,9,68,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5579 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5579
end Delivery.IrregularNine14.P07
