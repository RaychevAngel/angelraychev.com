import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0008

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6540 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 4, region := 386, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(4,7)], upper := (rows 35 322 14 168 84 33 65 144 400), lower := (rows 35 322 14 168 84 33 65 128 256), losses := [] }

theorem u6540 : Upper (D 7) (R 7) [34,320,10,160,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6541 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 14 168 84 33 80 129 385), lower := (rows 35 322 14 168 84 33 80 128 256), losses := [] }

theorem u6541 : Upper (D 7) (R 7) [34,320,10,160,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6541 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6542 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,0)], upper := (rows 35 322 14 168 84 33 192 145 273), lower := (rows 35 322 14 168 84 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 32 200 128 256), good := (rows 34 322 94 232 84 32 192 192 256) }] }

theorem u6542 : Upper (D 7) (R 7) [34,320,10,160,68,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6543 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 322 14 168 208 33 65 148 276), lower := (rows 35 322 14 168 208 33 65 128 256), losses := [{ target := 0, region := (rows 0 82 69 41 82 32 64 215 343), good := (rows 446 470 414 168 470 428 478 128 256) }] }

theorem u6543 : Upper (D 7) (R 7) [34,320,10,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6544 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,6),(0,7),(1,7)], upper := (rows 35 322 14 168 208 33 68 145 273), lower := (rows 35 322 14 168 208 33 68 128 256), losses := [] }

theorem u6544 : Upper (D 7) (R 7) [34,320,10,160,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6544 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6545 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 14 168 208 33 80 133 261), lower := (rows 35 322 14 168 208 33 80 128 256), losses := [] }

theorem u6545 : Upper (D 7) (R 7) [34,320,10,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6545 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6546 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 322 14 200 145 33 68 176 304), lower := (rows 35 322 14 200 145 33 68 128 256), losses := [] }

theorem u6546 : Upper (D 7) (R 7) [34,320,10,192,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6546 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6547 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 14 200 145 33 80 164 292), lower := (rows 35 322 14 200 145 33 80 128 256), losses := [] }

theorem u6547 : Upper (D 7) (R 7) [34,320,10,192,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6547 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6548 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 14 200 145 33 96 148 276), lower := (rows 35 322 14 200 145 33 96 128 256), losses := [] }

theorem u6548 : Upper (D 7) (R 7) [34,320,10,192,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6549 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 72, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 322 14 200 145 48 65 164 292), lower := (rows 35 322 14 200 145 48 65 128 256), losses := [] }

theorem u6549 : Upper (D 7) (R 7) [34,320,10,192,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6549 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6550 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 144, targets := 66 }], pairs := [(4,1),(4,6)], upper := (rows 35 322 14 200 145 48 68 161 289), lower := (rows 35 322 14 200 145 48 68 128 256), losses := [] }

theorem u6550 : Upper (D 7) (R 7) [34,320,10,192,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6550 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6551 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 104, targets := 1 }], pairs := [(0,6),(3,0),(4,6)], upper := (rows 35 322 14 200 145 48 96 133 261), lower := (rows 35 322 14 200 145 48 96 128 256), losses := [] }

theorem u6551 : Upper (D 7) (R 7) [34,320,10,192,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6551 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6552 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 14 200 176 33 65 148 276), lower := (rows 35 322 14 200 176 33 65 128 256), losses := [] }

theorem u6552 : Upper (D 7) (R 7) [34,320,10,192,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6553 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 322 14 200 176 33 68 145 273), lower := (rows 35 322 14 200 176 33 68 128 256), losses := [] }

theorem u6553 : Upper (D 7) (R 7) [34,320,10,192,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6553 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6554 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 14 200 176 33 80 133 261), lower := (rows 35 322 14 200 176 33 80 128 256), losses := [] }

theorem u6554 : Upper (D 7) (R 7) [34,320,10,192,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6554 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6555 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 180, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 35 322 28 73 145 160 66 164 292), lower := (rows 35 322 28 73 145 160 66 128 256), losses := [] }

theorem u6555 : Upper (D 7) (R 7) [34,320,24,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6556 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 322 28 73 145 160 68 162 290), lower := (rows 35 322 28 73 145 160 68 128 256), losses := [] }

theorem u6556 : Upper (D 7) (R 7) [34,320,24,65,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6556 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6557 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 322 28 73 145 160 96 134 262), lower := (rows 35 322 28 73 145 160 96 128 256), losses := [] }

theorem u6557 : Upper (D 7) (R 7) [34,320,24,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6558 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 35 322 28 73 146 160 65 164 292), lower := (rows 35 322 28 73 146 160 65 128 256), losses := [] }

theorem u6558 : Upper (D 7) (R 7) [34,320,24,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6559 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 322 28 73 146 160 68 161 289), lower := (rows 35 322 28 73 146 160 68 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 255 0 159 287), good := (rows 435 435 445 445 435 160 420 160 256) }] }

theorem u6559 : Upper (D 7) (R 7) [34,320,24,65,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6559 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6560 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 322 28 73 146 160 96 133 261), lower := (rows 35 322 28 73 146 160 96 128 256), losses := [] }

theorem u6560 : Upper (D 7) (R 7) [34,320,24,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6561 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 322 28 76 146 33 65 160 416), lower := (rows 35 322 28 76 146 33 65 128 256), losses := [] }

theorem u6561 : Upper (D 7) (R 7) [34,320,24,68,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6562 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 322 28 76 146 33 96 129 385), lower := (rows 35 322 28 76 146 33 96 128 256), losses := [] }

theorem u6562 : Upper (D 7) (R 7) [34,320,24,68,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6563 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 76, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(3,0)], upper := (rows 35 322 28 76 146 33 192 161 289), lower := (rows 35 322 28 76 146 33 192 128 256), losses := [] }

theorem u6563 : Upper (D 7) (R 7) [34,320,24,68,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6564 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 4, region := 108, targets := 2 }], pairs := [(1,5),(2,1),(3,1),(3,7)], upper := (rows 35 322 28 104 145 160 65 134 262), lower := (rows 35 322 28 104 145 160 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 81 132 260), good := (rows 67 322 478 72 209 128 65 128 256) }] }

theorem u6564 : Upper (D 7) (R 7) [34,320,24,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6565 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 0, region := 72, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 35 322 28 104 145 160 66 133 261), lower := (rows 35 322 28 104 145 160 66 128 256), losses := [] }

theorem u6565 : Upper (D 7) (R 7) [34,320,24,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6566 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 322 28 104 145 160 68 131 259), lower := (rows 35 322 28 104 145 160 68 128 256), losses := [] }

theorem u6566 : Upper (D 7) (R 7) [34,320,24,96,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6566 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6567 : Route 9 := (fun mask => (mask,id))

def c6567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6567 : Upper (D 7) (R 7) [34,320,24,96,130,128,1] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96,130,128,1] 13 (by decide) (choices 1) [1,4] r6567 c6567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u486
  · exact u487

def b6568 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 322 28 104 146 160 68 129 257), lower := (rows 35 322 28 104 146 160 68 128 256), losses := [] }

theorem u6568 : Upper (D 7) (R 7) [34,320,24,96,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6568 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6569 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 8, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 322 28 137 208 33 66 164 292), lower := (rows 35 322 28 137 208 33 66 128 256), losses := [] }

theorem u6569 : Upper (D 7) (R 7) [34,320,24,129,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6570 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 35 322 28 137 208 33 68 162 290), lower := (rows 35 322 28 137 208 33 68 128 256), losses := [] }

theorem u6570 : Upper (D 7) (R 7) [34,320,24,129,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6570 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6571 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 116, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(4,1)], upper := (rows 35 322 28 137 208 33 96 134 262), lower := (rows 35 322 28 137 208 33 96 128 256), losses := [] }

theorem u6571 : Upper (D 7) (R 7) [34,320,24,129,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6572 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 322 28 138 208 33 65 164 292), lower := (rows 35 322 28 138 208 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 86 89 80 32 64 129 257), good := (rows 430 350 28 142 222 424 478 128 256) }] }

theorem u6572 : Upper (D 7) (R 7) [34,320,24,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6573 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 322 28 138 208 33 68 161 289), lower := (rows 35 322 28 138 208 33 68 128 256), losses := [] }

theorem u6573 : Upper (D 7) (R 7) [34,320,24,130,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6573 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6574 : Route 9 := (fun mask => (mask,id))

def c6574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6574 : Upper (D 7) (R 7) [34,320,24,130,192,1,32] 13 := by
  apply FastRouting.sound _ _ [34,320,24,130,192,1,32] 13 (by decide) (choices 1) [1,4] r6574 c6574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u488
  · exact u489

def b6575 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 322 28 168 208 33 65 134 262), lower := (rows 35 322 28 168 208 33 65 128 256), losses := [{ target := 0, region := (rows 0 82 69 41 82 32 64 215 343), good := (rows 446 470 414 168 470 428 478 128 256) }] }

theorem u6575 : Upper (D 7) (R 7) [34,320,24,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6576 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 8, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 322 28 168 208 33 66 133 261), lower := (rows 35 322 28 168 208 33 66 128 256), losses := [] }

theorem u6576 : Upper (D 7) (R 7) [34,320,24,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6577 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 322 28 168 208 33 68 131 259), lower := (rows 35 322 28 168 208 33 68 128 256), losses := [] }

theorem u6577 : Upper (D 7) (R 7) [34,320,24,160,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6577 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6578 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 180, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 322 44 73 145 48 66 132 388), lower := (rows 35 322 44 73 145 48 66 128 256), losses := [] }

theorem u6578 : Upper (D 7) (R 7) [34,320,40,65,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6578 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6579 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7)], upper := (rows 35 322 44 73 145 48 68 130 386), lower := (rows 35 322 44 73 145 48 68 128 256), losses := [] }

theorem u6579 : Upper (D 7) (R 7) [34,320,40,65,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6579 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6580 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 4, region := 108, targets := 2 }], pairs := [(1,0),(1,5),(2,1)], upper := (rows 35 322 44 73 145 48 192 134 262), lower := (rows 35 322 44 73 145 48 192 128 256), losses := [] }

theorem u6580 : Upper (D 7) (R 7) [34,320,40,65,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6580 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6581 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 180, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 35 322 44 73 145 160 66 148 276), lower := (rows 35 322 44 73 145 160 66 128 256), losses := [] }

theorem u6581 : Upper (D 7) (R 7) [34,320,40,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6582 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 322 44 73 145 160 68 146 274), lower := (rows 35 322 44 73 145 160 68 128 256), losses := [] }

theorem u6582 : Upper (D 7) (R 7) [34,320,40,65,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6582 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6583 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 4, region := 108, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 35 322 44 73 145 160 80 134 262), lower := (rows 35 322 44 73 145 160 80 128 256), losses := [] }

theorem u6583 : Upper (D 7) (R 7) [34,320,40,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6583 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6584 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 322 44 73 146 160 65 148 276), lower := (rows 35 322 44 73 146 160 65 128 256), losses := [] }

theorem u6584 : Upper (D 7) (R 7) [34,320,40,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6585 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 322 44 73 146 160 68 145 273), lower := (rows 35 322 44 73 146 160 68 128 256), losses := [] }

theorem u6585 : Upper (D 7) (R 7) [34,320,40,65,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6585 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6586 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 164, targets := 66 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(2,6)], upper := (rows 35 322 44 73 146 160 80 133 261), lower := (rows 35 322 44 73 146 160 80 128 256), losses := [] }

theorem u6586 : Upper (D 7) (R 7) [34,320,40,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6586 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6587 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 322 44 73 148 160 65 146 274), lower := (rows 35 322 44 73 148 160 65 128 256), losses := [] }

theorem u6587 : Upper (D 7) (R 7) [34,320,40,65,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6588 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 180, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 35 322 44 73 148 160 66 145 273), lower := (rows 35 322 44 73 148 160 66 128 256), losses := [] }

theorem u6588 : Upper (D 7) (R 7) [34,320,40,65,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6589 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 161, targets := 64 },{ cop := 3, region := 258, targets := 32 },{ cop := 3, region := 258, targets := 128 }], pairs := [(0,6),(1,5),(1,7)], upper := (rows 35 322 44 73 148 160 80 131 259), lower := (rows 35 322 44 73 148 160 80 128 256), losses := [] }

theorem u6589 : Upper (D 7) (R 7) [34,320,40,65,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6589 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6590 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 66, targets := 33 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 322 44 200 145 33 66 148 276), lower := (rows 35 322 44 200 145 33 66 128 256), losses := [] }

theorem u6590 : Upper (D 7) (R 7) [34,320,40,192,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6591 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 4, region := 108, targets := 2 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 35 322 44 200 145 33 68 146 274), lower := (rows 35 322 44 200 145 33 68 128 256), losses := [] }

theorem u6591 : Upper (D 7) (R 7) [34,320,40,192,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6591 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6592 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 44 200 145 33 80 134 262), lower := (rows 35 322 44 200 145 33 80 128 256), losses := [] }

theorem u6592 : Upper (D 7) (R 7) [34,320,40,192,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6592 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6593 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 4, region := 108, targets := 2 }], pairs := [(0,7),(1,7),(2,1)], upper := (rows 35 322 44 200 145 48 65 134 262), lower := (rows 35 322 44 200 145 48 65 128 256), losses := [] }

theorem u6593 : Upper (D 7) (R 7) [34,320,40,192,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6593 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6594 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 322 44 200 145 48 66 133 261), lower := (rows 35 322 44 200 145 48 66 128 256), losses := [] }

theorem u6594 : Upper (D 7) (R 7) [34,320,40,192,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6594 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6595 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 322 44 200 145 48 68 131 259), lower := (rows 35 322 44 200 145 48 68 128 256), losses := [] }

theorem u6595 : Upper (D 7) (R 7) [34,320,40,192,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6595 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6596 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 322 44 200 146 33 65 148 276), lower := (rows 35 322 44 200 146 33 65 128 256), losses := [{ target := 0, region := (rows 0 74 5 74 95 32 64 229 357), good := (rows 446 474 446 474 154 436 478 128 256) }] }

theorem u6596 : Upper (D 7) (R 7) [34,320,40,192,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6597 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,6),(4,5),(4,6)], upper := (rows 35 322 44 200 146 33 68 145 273), lower := (rows 35 322 44 200 146 33 68 128 256), losses := [] }

theorem u6597 : Upper (D 7) (R 7) [34,320,40,192,130,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6597 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6598 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 44 200 146 33 80 133 261), lower := (rows 35 322 44 200 146 33 80 128 256), losses := [] }

theorem u6598 : Upper (D 7) (R 7) [34,320,40,192,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6598 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6599 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 322 44 200 148 33 65 146 274), lower := (rows 35 322 44 200 148 33 65 128 256), losses := [{ target := 0, region := (rows 0 74 5 74 117 32 64 207 335), good := (rows 446 474 446 474 404 436 478 128 256) }] }

theorem u6599 : Upper (D 7) (R 7) [34,320,40,192,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6599
end Delivery.IrregularNine14.P07
