import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0008

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6540 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 25 336 36 68 162 290), lower := (rows 35 131 76 25 336 36 68 128 256), losses := [] }

theorem u6540 : Upper (D 6) (R 6) [34,129,72,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6541 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 3, region := 100, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 76 25 336 36 96 134 262), lower := (rows 35 131 76 25 336 36 96 128 256), losses := [] }

theorem u6541 : Upper (D 6) (R 6) [34,129,72,17,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6542 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 387, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 26 21 96 68 416 288), lower := (rows 35 131 76 26 21 96 68 128 256), losses := [] }

theorem u6542 : Upper (D 6) (R 6) [34,129,72,18,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6543 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 131 76 26 21 96 96 388 260), lower := (rows 35 131 76 26 21 96 96 128 256), losses := [] }

theorem u6543 : Upper (D 6) (R 6) [34,129,72,18,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6544 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 76 26 21 96 320 164 292), lower := (rows 35 131 76 26 21 96 320 128 256), losses := [] }

theorem u6544 : Upper (D 6) (R 6) [34,129,72,18,5,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6544 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6545 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 304, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 76 26 52 288 65 196 324), lower := (rows 35 131 76 26 52 288 65 128 256), losses := [] }

theorem u6545 : Upper (D 6) (R 6) [34,129,72,18,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6545 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6546 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 26 52 288 68 193 321), lower := (rows 35 131 76 26 52 288 68 128 256), losses := [] }

theorem u6546 : Upper (D 6) (R 6) [34,129,72,18,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6546 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6547 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 3, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 26 273 96 68 164 292), lower := (rows 35 131 76 26 273 96 68 128 256), losses := [] }

theorem u6547 : Upper (D 6) (R 6) [34,129,72,18,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6548 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 76 26 273 96 96 132 260), lower := (rows 35 131 76 26 273 96 96 128 256), losses := [] }

theorem u6548 : Upper (D 6) (R 6) [34,129,72,18,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6549 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 76 26 276 96 65 164 292), lower := (rows 35 131 76 26 276 96 65 128 256), losses := [] }

theorem u6549 : Upper (D 6) (R 6) [34,129,72,18,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6550 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 26 276 96 68 161 289), lower := (rows 35 131 76 26 276 96 68 128 256), losses := [] }

theorem u6550 : Upper (D 6) (R 6) [34,129,72,18,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6551 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 76 26 276 96 96 133 261), lower := (rows 35 131 76 26 276 96 96 128 256), losses := [] }

theorem u6551 : Upper (D 6) (R 6) [34,129,72,18,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6552 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 304, targets := 3 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 35 131 76 26 304 36 65 196 324), lower := (rows 35 131 76 26 304 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 9 116 100 64 196 324), good := (rows 58 138 508 26 304 436 508 128 256) }] }

theorem u6552 : Upper (D 6) (R 6) [34,129,72,18,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6553 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 3, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 26 304 36 68 193 321), lower := (rows 35 131 76 26 304 36 68 128 256), losses := [] }

theorem u6553 : Upper (D 6) (R 6) [34,129,72,18,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6554 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 76 26 304 96 65 132 260), lower := (rows 35 131 76 26 304 96 65 128 256), losses := [] }

theorem u6554 : Upper (D 6) (R 6) [34,129,72,18,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6555 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 3, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 26 304 96 68 133 261), lower := (rows 35 131 76 26 304 96 68 128 256), losses := [] }

theorem u6555 : Upper (D 6) (R 6) [34,129,72,18,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6556 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 76 26 336 36 65 164 292), lower := (rows 35 131 76 26 336 36 65 128 256), losses := [] }

theorem u6556 : Upper (D 6) (R 6) [34,129,72,18,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6557 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 26 336 36 68 161 289), lower := (rows 35 131 76 26 336 36 68 128 256), losses := [] }

theorem u6557 : Upper (D 6) (R 6) [34,129,72,18,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6558 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 3, region := 100, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 76 26 336 36 96 133 261), lower := (rows 35 131 76 26 336 36 96 128 256), losses := [] }

theorem u6558 : Upper (D 6) (R 6) [34,129,72,18,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6559 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 76 28 273 96 66 164 292), lower := (rows 35 131 76 28 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 119 67 156 284), good := (rows 98 226 492 444 508 96 98 128 256) }] }

theorem u6559 : Upper (D 6) (R 6) [34,129,72,20,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6560 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 28 273 96 68 162 290), lower := (rows 35 131 76 28 273 96 68 128 256), losses := [] }

theorem u6560 : Upper (D 6) (R 6) [34,129,72,20,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6561 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 28 273 96 96 134 262), lower := (rows 35 131 76 28 273 96 96 128 256), losses := [] }

theorem u6561 : Upper (D 6) (R 6) [34,129,72,20,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6562 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 76 28 274 96 65 164 292), lower := (rows 35 131 76 28 274 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 100 73 19 100 64 237 365), good := (rows 446 410 492 444 274 492 508 128 256) }] }

theorem u6562 : Upper (D 6) (R 6) [34,129,72,20,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6563 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 28 274 96 68 161 289), lower := (rows 35 131 76 28 274 96 68 128 256), losses := [] }

theorem u6563 : Upper (D 6) (R 6) [34,129,72,20,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6564 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 28 274 96 96 133 261), lower := (rows 35 131 76 28 274 96 96 128 256), losses := [] }

theorem u6564 : Upper (D 6) (R 6) [34,129,72,20,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6565 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 76 28 304 96 65 134 262), lower := (rows 35 131 76 28 304 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 100 125 81 100 64 129 257), good := (rows 446 410 124 60 316 124 508 128 256) }] }

theorem u6565 : Upper (D 6) (R 6) [34,129,72,20,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6566 : Route 9 := (fun mask => (mask,id))

def c6566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6566 : Upper (D 6) (R 6) [34,129,72,20,288,64,2] 13 := by
  apply FastRouting.sound _ _ [34,129,72,20,288,64,2] 13 (by decide) (choices 1) [1,4] r6566 c6566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u483
  · exact u484

def b6567 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 28 304 96 68 131 259), lower := (rows 35 131 76 28 304 96 68 128 256), losses := [] }

theorem u6567 : Upper (D 6) (R 6) [34,129,72,20,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6568 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 76 44 81 288 66 148 276), lower := (rows 35 131 76 44 81 288 66 128 256), losses := [] }

theorem u6568 : Upper (D 6) (R 6) [34,129,72,36,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6568 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6569 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 419, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 44 81 288 68 146 274), lower := (rows 35 131 76 44 81 288 68 128 256), losses := [] }

theorem u6569 : Upper (D 6) (R 6) [34,129,72,36,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6569 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6570 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1)], upper := (rows 35 131 76 44 81 288 80 134 262), lower := (rows 35 131 76 44 81 288 80 128 256), losses := [] }

theorem u6570 : Upper (D 6) (R 6) [34,129,72,36,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6570 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6571 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 76 44 82 288 65 148 276), lower := (rows 35 131 76 44 82 288 65 128 256), losses := [] }

theorem u6571 : Upper (D 6) (R 6) [34,129,72,36,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6571 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6572 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 289, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 44 82 288 68 145 273), lower := (rows 35 131 76 44 82 288 68 128 256), losses := [] }

theorem u6572 : Upper (D 6) (R 6) [34,129,72,36,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6572 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6573 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0)], upper := (rows 35 131 76 44 82 288 80 133 261), lower := (rows 35 131 76 44 82 288 80 128 256), losses := [] }

theorem u6573 : Upper (D 6) (R 6) [34,129,72,36,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6573 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6574 : PairBound 9 := { available := 68, camps := [], pairs := [(2,1),(3,0)], upper := (rows 35 131 76 56 22 288 65 196 324), lower := (rows 35 131 76 56 22 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 308 64 132 260), good := (rows 34 130 492 56 446 288 64 128 288) },{ target := 1, region := (rows 1 0 20 24 16 316 67 148 276), good := (rows 97 193 492 444 508 288 65 128 288) }] }

theorem u6574 : Upper (D 6) (R 6) [34,129,72,48,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6574 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6575 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 56 22 288 68 193 321), lower := (rows 35 131 76 56 22 288 68 128 256), losses := [] }

theorem u6575 : Upper (D 6) (R 6) [34,129,72,48,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6575 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6576 : Route 9 := (fun mask => (mask,id))

def c6576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6576 : Upper (D 6) (R 6) [34,129,72,48,257,4,2] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,257,4,2] 13 (by decide) (choices 1) [4,64] r6576 c6576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u485
  · exact u486

def b6577 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 56 273 36 68 194 322), lower := (rows 35 131 76 56 273 36 68 128 256), losses := [] }

theorem u6577 : Upper (D 6) (R 6) [34,129,72,48,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6578 : PairBound 9 := { available := 4, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 76 56 273 96 66 132 260), lower := (rows 35 131 76 56 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 119 67 156 284), good := (rows 98 226 492 444 508 96 98 128 256) }] }

theorem u6578 : Upper (D 6) (R 6) [34,129,72,48,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6579 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 56 273 96 68 134 262), lower := (rows 35 131 76 56 273 96 68 128 256), losses := [] }

theorem u6579 : Upper (D 6) (R 6) [34,129,72,48,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6580 : Route 9 := (fun mask => (mask,id))

def c6580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6580 : Upper (D 6) (R 6) [34,129,72,48,258,4,1] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,258,4,1] 13 (by decide) (choices 1) [4,64] r6580 c6580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u487
  · exact u488

def b6581 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 56 274 36 68 193 321), lower := (rows 35 131 76 56 274 36 68 128 256), losses := [] }

theorem u6581 : Upper (D 6) (R 6) [34,129,72,48,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6582 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 105, targets := 4 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 76 56 274 96 65 132 260), lower := (rows 35 131 76 56 274 96 65 128 256), losses := [] }

theorem u6582 : Upper (D 6) (R 6) [34,129,72,48,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6583 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 56 274 96 68 133 261), lower := (rows 35 131 76 56 274 96 68 128 256), losses := [] }

theorem u6583 : Upper (D 6) (R 6) [34,129,72,48,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6584 : Route 9 := (fun mask => (mask,id))

def c6584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u6584 : Upper (D 6) (R 6) [34,129,72,257,6,4,16] 13 := by
  apply FastRouting.sound _ _ [34,129,72,257,6,4,16] 13 (by decide) (choices 1) [32,64] r6584 c6584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u489
  · exact u490

def b6585 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 76 265 22 36 96 208 336), lower := (rows 35 131 76 265 22 36 96 128 256), losses := [] }

theorem u6585 : Upper (D 6) (R 6) [34,129,72,257,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6586 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 3, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 265 22 96 68 176 304), lower := (rows 35 131 76 265 22 96 68 128 256), losses := [] }

theorem u6586 : Upper (D 6) (R 6) [34,129,72,257,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6587 : Route 9 := (fun mask => (mask,id))

def c6587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6587 : Upper (D 6) (R 6) [34,129,72,257,6,64,16] 13 := by
  apply FastRouting.sound _ _ [34,129,72,257,6,64,16] 13 (by decide) (choices 1) [4,32] r6587 c6587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u491
  · exact u492

def b6588 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 76 265 22 96 96 148 276), lower := (rows 35 131 76 265 22 96 96 128 256), losses := [] }

theorem u6588 : Upper (D 6) (R 6) [34,129,72,257,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6589 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 3, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 265 82 36 68 176 304), lower := (rows 35 131 76 265 82 36 68 128 256), losses := [] }

theorem u6589 : Upper (D 6) (R 6) [34,129,72,257,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6590 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 35 131 76 265 82 36 80 164 292), lower := (rows 35 131 76 265 82 36 80 128 256), losses := [] }

theorem u6590 : Upper (D 6) (R 6) [34,129,72,257,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6590 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6591 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 0, region := 80, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 76 265 82 36 96 148 276), lower := (rows 35 131 76 265 82 36 96 128 256), losses := [] }

theorem u6591 : Upper (D 6) (R 6) [34,129,72,257,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6592 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 80, targets := 4 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 76 265 112 36 66 148 276), lower := (rows 35 131 76 265 112 36 66 128 256), losses := [] }

theorem u6592 : Upper (D 6) (R 6) [34,129,72,257,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6593 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 265 112 36 68 146 274), lower := (rows 35 131 76 265 112 36 68 128 256), losses := [] }

theorem u6593 : Upper (D 6) (R 6) [34,129,72,257,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6594 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 76 265 112 36 80 134 262), lower := (rows 35 131 76 265 112 36 80 128 256), losses := [] }

theorem u6594 : Upper (D 6) (R 6) [34,129,72,257,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6594 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6595 : Route 9 := (fun mask => (mask,id))

def c6595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u6595 : Upper (D 6) (R 6) [34,129,72,258,5,4,16] 13 := by
  apply FastRouting.sound _ _ [34,129,72,258,5,4,16] 13 (by decide) (choices 1) [32,64] r6595 c6595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u493
  · exact u494

def b6596 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 100, targets := 3 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 35 131 76 266 21 36 96 208 336), lower := (rows 35 131 76 266 21 36 96 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 32 97 144 272), good := (rows 99 195 72 266 475 96 96 128 256) }] }

theorem u6596 : Upper (D 6) (R 6) [34,129,72,258,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6597 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 3, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 266 21 96 68 176 304), lower := (rows 35 131 76 266 21 96 68 128 256), losses := [] }

theorem u6597 : Upper (D 6) (R 6) [34,129,72,258,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6598 : Route 9 := (fun mask => (mask,id))

def c6598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6598 : Upper (D 6) (R 6) [34,129,72,258,5,64,16] 13 := by
  apply FastRouting.sound _ _ [34,129,72,258,5,64,16] 13 (by decide) (choices 1) [4,32] r6598 c6598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u495
  · exact u496

def b6599 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 131 76 266 21 96 96 148 276), lower := (rows 35 131 76 266 21 96 96 128 256), losses := [] }

theorem u6599 : Upper (D 6) (R 6) [34,129,72,258,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6599
end Delivery.IrregularNine14.P06
