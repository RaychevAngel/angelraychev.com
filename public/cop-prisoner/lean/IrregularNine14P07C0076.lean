import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0005

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4560 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 69 138 112 160 66 145 273), lower := (rows 13 290 69 138 112 160 66 128 256), losses := [] }

theorem u4560 : Upper (D 7) (R 7) [12,288,65,130,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4561 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 290 69 138 112 160 80 131 259), lower := (rows 13 290 69 138 112 160 80 128 256), losses := [] }

theorem u4561 : Upper (D 7) (R 7) [12,288,65,130,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4561 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4562 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 290 69 138 176 96 65 146 274), lower := (rows 13 290 69 138 176 96 65 128 256), losses := [] }

theorem u4562 : Upper (D 7) (R 7) [12,288,65,130,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4563 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 69 138 176 96 66 145 273), lower := (rows 13 290 69 138 176 96 66 128 256), losses := [] }

theorem u4563 : Upper (D 7) (R 7) [12,288,65,130,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4564 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 13 290 69 138 176 96 80 131 259), lower := (rows 13 290 69 138 176 96 80 128 256), losses := [] }

theorem u4564 : Upper (D 7) (R 7) [12,288,65,130,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4564 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4565 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 85, targets := 32 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 13 290 69 138 208 33 66 176 304), lower := (rows 13 290 69 138 208 33 66 128 256), losses := [] }

theorem u4565 : Upper (D 7) (R 7) [12,288,65,130,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4566 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 290 69 138 208 33 80 162 290), lower := (rows 13 290 69 138 208 33 80 128 256), losses := [] }

theorem u4566 : Upper (D 7) (R 7) [12,288,65,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4566 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4567 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 117, targets := 2 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 13 290 69 138 208 33 96 146 274), lower := (rows 13 290 69 138 208 33 96 128 256), losses := [] }

theorem u4567 : Upper (D 7) (R 7) [12,288,65,130,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4568 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 69 138 208 34 65 176 304), lower := (rows 13 290 69 138 208 34 65 128 256), losses := [] }

theorem u4568 : Upper (D 7) (R 7) [12,288,65,130,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4569 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 85, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 13 290 69 138 208 34 80 161 289), lower := (rows 13 290 69 138 208 34 80 128 256), losses := [] }

theorem u4569 : Upper (D 7) (R 7) [12,288,65,130,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4569 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4570 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 144, targets := 34 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,1),(4,5)], upper := (rows 13 290 69 138 208 34 96 145 273), lower := (rows 13 290 69 138 208 34 96 128 256), losses := [] }

theorem u4570 : Upper (D 7) (R 7) [12,288,65,130,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4571 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 13 290 69 138 208 48 65 162 290), lower := (rows 13 290 69 138 208 48 65 128 256), losses := [] }

theorem u4571 : Upper (D 7) (R 7) [12,288,65,130,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4571 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4572 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 13 290 69 138 208 48 66 161 289), lower := (rows 13 290 69 138 208 48 66 128 256), losses := [] }

theorem u4572 : Upper (D 7) (R 7) [12,288,65,130,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4572 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4573 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 13 290 69 138 208 48 96 131 259), lower := (rows 13 290 69 138 208 48 96 128 256), losses := [] }

theorem u4573 : Upper (D 7) (R 7) [12,288,65,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4573 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4574 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 69, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 69 152 82 34 65 160 416), lower := (rows 13 290 69 152 82 34 65 128 256), losses := [] }

theorem u4574 : Upper (D 7) (R 7) [12,288,65,144,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4575 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 141, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 69 152 82 34 96 129 385), lower := (rows 13 290 69 152 82 34 96 128 256), losses := [] }

theorem u4575 : Upper (D 7) (R 7) [12,288,65,144,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4576 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 69 152 82 34 192 161 289), lower := (rows 13 290 69 152 82 34 192 128 256), losses := [] }

theorem u4576 : Upper (D 7) (R 7) [12,288,65,144,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4577 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 69 152 82 160 65 162 290), lower := (rows 13 290 69 152 82 160 65 128 256), losses := [] }

theorem u4577 : Upper (D 7) (R 7) [12,288,65,144,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4578 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 173, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 13 290 69 152 82 160 66 161 289), lower := (rows 13 290 69 152 82 160 66 128 256), losses := [] }

theorem u4578 : Upper (D 7) (R 7) [12,288,65,144,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4579 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 13 290 69 152 82 160 96 131 259), lower := (rows 13 290 69 152 82 160 96 128 256), losses := [] }

theorem u4579 : Upper (D 7) (R 7) [12,288,65,144,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4580 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 69 152 112 34 65 130 386), lower := (rows 13 290 69 152 112 34 65 128 256), losses := [] }

theorem u4580 : Upper (D 7) (R 7) [12,288,65,144,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4581 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 141, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 69 152 112 34 66 129 385), lower := (rows 13 290 69 152 112 34 66 128 256), losses := [] }

theorem u4581 : Upper (D 7) (R 7) [12,288,65,144,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4582 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 69 152 112 34 192 131 259), lower := (rows 13 290 69 152 112 34 192 128 256), losses := [] }

theorem u4582 : Upper (D 7) (R 7) [12,288,65,144,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4583 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 69 152 112 160 65 130 258), lower := (rows 13 290 69 152 112 160 65 128 256), losses := [] }

theorem u4583 : Upper (D 7) (R 7) [12,288,65,144,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4584 : Route 9 := (fun mask => (mask,id))

def c4584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4584 : Upper (D 7) (R 7) [12,288,65,144,96,128,2] 13 := by
  apply FastRouting.sound _ _ [12,288,65,144,96,128,2] 13 (by decide) (choices 1) [1,2] r4584 c4584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u351
  · exact u352

def b4585 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 68, targets := 32 },{ cop := 4, region := 68, targets := 128 }], pairs := [(1,0),(2,5),(2,7),(3,0)], upper := (rows 13 290 69 168 19 96 66 144 400), lower := (rows 13 290 69 168 19 96 66 128 256), losses := [] }

theorem u4585 : Upper (D 7) (R 7) [12,288,65,160,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4586 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 13 290 69 168 19 96 80 130 386), lower := (rows 13 290 69 168 19 96 80 128 256), losses := [] }

theorem u4586 : Upper (D 7) (R 7) [12,288,65,160,3,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4586 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4587 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 45, targets := 2 },{ cop := 2, region := 306, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(3,1)], upper := (rows 13 290 69 168 19 96 192 146 274), lower := (rows 13 290 69 168 19 96 192 128 256), losses := [] }

theorem u4587 : Upper (D 7) (R 7) [12,288,65,160,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4588 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 69 168 82 34 65 144 400), lower := (rows 13 290 69 168 82 34 65 128 256), losses := [] }

theorem u4588 : Upper (D 7) (R 7) [12,288,65,160,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4589 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 290 69 168 82 34 80 129 385), lower := (rows 13 290 69 168 82 34 80 128 256), losses := [] }

theorem u4589 : Upper (D 7) (R 7) [12,288,65,160,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4589 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4590 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 69 168 82 34 192 145 273), lower := (rows 13 290 69 168 82 34 192 128 256), losses := [] }

theorem u4590 : Upper (D 7) (R 7) [12,288,65,160,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4591 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 162 }], pairs := [(0,1),(0,5),(0,7)], upper := (rows 13 290 69 168 82 48 65 130 386), lower := (rows 13 290 69 168 82 48 65 128 256), losses := [] }

theorem u4591 : Upper (D 7) (R 7) [12,288,65,160,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4591 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4592 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 290 69 168 82 48 66 129 385), lower := (rows 13 290 69 168 82 48 66 128 256), losses := [] }

theorem u4592 : Upper (D 7) (R 7) [12,288,65,160,66,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4592 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4593 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 13 290 69 168 82 48 192 131 259), lower := (rows 13 290 69 168 82 48 192 128 256), losses := [] }

theorem u4593 : Upper (D 7) (R 7) [12,288,65,160,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4593 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4594 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 290 69 168 146 96 65 146 274), lower := (rows 13 290 69 168 146 96 65 128 256), losses := [] }

theorem u4594 : Upper (D 7) (R 7) [12,288,65,160,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4595 : Route 9 := (fun mask => (mask,id))

def c4595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4595 : Upper (D 7) (R 7) [12,288,65,160,130,64,2] 13 := by
  apply FastRouting.sound _ _ [12,288,65,160,130,64,2] 13 (by decide) (choices 1) [1,16] r4595 c4595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u353
  · exact u354

def b4596 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 290 69 168 146 96 80 131 259), lower := (rows 13 290 69 168 146 96 80 128 256), losses := [] }

theorem u4596 : Upper (D 7) (R 7) [12,288,65,160,130,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4596 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4597 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 69 168 208 34 65 146 274), lower := (rows 13 290 69 168 208 34 65 128 256), losses := [] }

theorem u4597 : Upper (D 7) (R 7) [12,288,65,160,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4598 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 144, targets := 34 },{ cop := 8, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 290 69 168 208 34 66 145 273), lower := (rows 13 290 69 168 208 34 66 128 256), losses := [] }

theorem u4598 : Upper (D 7) (R 7) [12,288,65,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4599 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 85, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 13 290 69 168 208 34 80 131 259), lower := (rows 13 290 69 168 208 34 80 128 256), losses := [] }

theorem u4599 : Upper (D 7) (R 7) [12,288,65,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4599 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4600 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 70 88 49 160 65 130 386), lower := (rows 13 290 70 88 49 160 65 128 256), losses := [] }

theorem u4600 : Upper (D 7) (R 7) [12,288,66,80,33,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4601 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 70 88 49 160 66 129 385), lower := (rows 13 290 70 88 49 160 66 128 256), losses := [] }

theorem u4601 : Upper (D 7) (R 7) [12,288,66,80,33,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4602 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 258, targets := 128 }], pairs := [(1,6),(1,7),(2,0),(4,6)], upper := (rows 13 290 70 88 49 160 192 131 259), lower := (rows 13 290 70 88 49 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 24 16 224 224 128 256), good := (rows 12 358 102 120 120 224 224 224 256) }] }

theorem u4602 : Upper (D 7) (R 7) [12,288,66,80,33,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4603 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(1,6),(2,0),(4,6)], upper := (rows 13 290 70 88 145 160 65 162 290), lower := (rows 13 290 70 88 145 160 65 128 256), losses := [] }

theorem u4603 : Upper (D 7) (R 7) [12,288,66,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4604 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 290 70 88 145 160 66 161 289), lower := (rows 13 290 70 88 145 160 66 128 256), losses := [] }

theorem u4604 : Upper (D 7) (R 7) [12,288,66,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4605 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 153, targets := 32 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 290 70 88 145 160 96 131 259), lower := (rows 13 290 70 88 145 160 96 128 256), losses := [] }

theorem u4605 : Upper (D 7) (R 7) [12,288,66,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4606 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 290 70 88 146 33 65 160 416), lower := (rows 13 290 70 88 146 33 65 128 256), losses := [] }

theorem u4606 : Upper (D 7) (R 7) [12,288,66,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4607 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 153, targets := 32 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,5),(0,7),(3,5),(4,5)], upper := (rows 13 290 70 88 146 33 96 129 385), lower := (rows 13 290 70 88 146 33 96 128 256), losses := [] }

theorem u4607 : Upper (D 7) (R 7) [12,288,66,80,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4608 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 13 290 70 88 146 33 192 161 289), lower := (rows 13 290 70 88 146 33 192 128 256), losses := [] }

theorem u4608 : Upper (D 7) (R 7) [12,288,66,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4609 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 70 88 146 160 65 161 289), lower := (rows 13 290 70 88 146 160 65 128 256), losses := [] }

theorem u4609 : Upper (D 7) (R 7) [12,288,66,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4610 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 153, targets := 32 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 290 70 88 146 160 96 129 257), lower := (rows 13 290 70 88 146 160 96 128 256), losses := [] }

theorem u4610 : Upper (D 7) (R 7) [12,288,66,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4611 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 290 70 88 176 33 65 130 386), lower := (rows 13 290 70 88 176 33 65 128 256), losses := [] }

theorem u4611 : Upper (D 7) (R 7) [12,288,66,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4612 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 290 70 88 176 33 66 129 385), lower := (rows 13 290 70 88 176 33 66 128 256), losses := [] }

theorem u4612 : Upper (D 7) (R 7) [12,288,66,80,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4613 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 13 290 70 88 176 33 192 131 259), lower := (rows 13 290 70 88 176 33 192 128 256), losses := [] }

theorem u4613 : Upper (D 7) (R 7) [12,288,66,80,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4614 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 290 70 104 145 48 65 130 386), lower := (rows 13 290 70 104 145 48 65 128 256), losses := [] }

theorem u4614 : Upper (D 7) (R 7) [12,288,66,96,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4614 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4615 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 290 70 104 145 48 66 129 385), lower := (rows 13 290 70 104 145 48 66 128 256), losses := [] }

theorem u4615 : Upper (D 7) (R 7) [12,288,66,96,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4615 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4616 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 70 104 145 48 192 131 259), lower := (rows 13 290 70 104 145 48 192 128 256), losses := [] }

theorem u4616 : Upper (D 7) (R 7) [12,288,66,96,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4616 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4617 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 13 290 70 104 145 160 65 146 274), lower := (rows 13 290 70 104 145 160 65 128 256), losses := [] }

theorem u4617 : Upper (D 7) (R 7) [12,288,66,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4618 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 13 290 70 104 145 160 66 145 273), lower := (rows 13 290 70 104 145 160 66 128 256), losses := [] }

theorem u4618 : Upper (D 7) (R 7) [12,288,66,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4619 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 70 104 145 160 80 131 259), lower := (rows 13 290 70 104 145 160 80 128 256), losses := [] }

theorem u4619 : Upper (D 7) (R 7) [12,288,66,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4619 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4619
end Delivery.IrregularNine14.P07
