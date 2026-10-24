import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0010

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4560 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 292 56 152 34 193 193 449), lower := (rows 97 7 292 56 152 34 64 128 256), losses := [] }

theorem u4560 : Upper (D 8) (R 8) [96,5,288,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4560 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4561 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 56 152 96 195 131 387), lower := (rows 97 7 292 56 152 96 64 128 256), losses := [] }

theorem u4561 : Upper (D 8) (R 8) [96,5,288,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4562 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 292 56 152 160 67 195 323), lower := (rows 97 7 292 56 152 160 64 128 256), losses := [] }

theorem u4562 : Upper (D 8) (R 8) [96,5,288,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4563 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 56 208 33 202 138 394), lower := (rows 97 7 292 56 208 33 64 128 256), losses := [] }

theorem u4563 : Upper (D 8) (R 8) [96,5,288,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4564 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 7 292 56 208 34 201 137 393), lower := (rows 97 7 292 56 208 34 64 128 256), losses := [] }

theorem u4564 : Upper (D 8) (R 8) [96,5,288,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4564 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4565 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 7 292 56 208 40 195 131 387), lower := (rows 97 7 292 56 208 40 64 128 256), losses := [] }

theorem u4565 : Upper (D 8) (R 8) [96,5,288,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4565 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4566 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 56 208 160 75 139 267), lower := (rows 97 7 292 56 208 160 64 128 256), losses := [] }

theorem u4566 : Upper (D 8) (R 8) [96,5,288,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4567 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 97 7 292 74 145 40 240 176 432), lower := (rows 97 7 292 74 145 40 64 128 256), losses := [] }

theorem u4567 : Upper (D 8) (R 8) [96,5,288,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4567 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4568 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 97 7 292 74 145 48 232 168 424), lower := (rows 97 7 292 74 145 48 64 128 256), losses := [] }

theorem u4568 : Upper (D 8) (R 8) [96,5,288,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4568 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4569 : Route 9 := (fun mask => (mask,id))

def c4569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4569 : Upper (D 8) (R 8) [96,5,288,66,129,128] 13 := by
  apply FastRouting.sound _ _ [96,5,288,66,129,128] 13 (by decide) (choices 1) [8,16,32] r4569 c4569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u627
  · exact u628
  · exact u629

def b4570 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 74 152 33 240 176 432), lower := (rows 97 7 292 74 152 33 64 128 256), losses := [] }

theorem u4570 : Upper (D 8) (R 8) [96,5,288,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4571 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 292 74 152 48 225 161 417), lower := (rows 97 7 292 74 152 48 64 128 256), losses := [] }

theorem u4571 : Upper (D 8) (R 8) [96,5,288,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4571 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4572 : Route 9 := (fun mask => (mask,id))

def c4572 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4572 : Upper (D 8) (R 8) [96,5,288,66,136,128] 13 := by
  apply FastRouting.sound _ _ [96,5,288,66,136,128] 13 (by decide) (choices 1) [1,16,32] r4572 c4572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u630
  · exact u631
  · exact u632

def b4573 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 74 176 33 216 152 408), lower := (rows 97 7 292 74 176 33 64 128 256), losses := [] }

theorem u4573 : Upper (D 8) (R 8) [96,5,288,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4574 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 7 292 74 176 40 209 145 401), lower := (rows 97 7 292 74 176 40 64 128 256), losses := [] }

theorem u4574 : Upper (D 8) (R 8) [96,5,288,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4574 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4575 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 7 292 74 176 48 201 137 393), lower := (rows 97 7 292 74 176 48 64 128 256), losses := [] }

theorem u4575 : Upper (D 8) (R 8) [96,5,288,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4575 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4576 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 74 176 160 89 153 281), lower := (rows 97 7 292 74 176 160 64 128 256), losses := [] }

theorem u4576 : Upper (D 8) (R 8) [96,5,288,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4577 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 97 7 292 88 145 34 232 168 424), lower := (rows 97 7 292 88 145 34 64 128 256), losses := [] }

theorem u4577 : Upper (D 8) (R 8) [96,5,288,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4577 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4578 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 97 7 292 88 145 40 226 162 418), lower := (rows 97 7 292 88 145 40 64 128 256), losses := [] }

theorem u4578 : Upper (D 8) (R 8) [96,5,288,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4578 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4579 : Route 9 := (fun mask => (mask,id))

def c4579 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4579 : Upper (D 8) (R 8) [96,5,288,80,129,128] 13 := by
  apply FastRouting.sound _ _ [96,5,288,80,129,128] 13 (by decide) (choices 1) [2,8,32] r4579 c4579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u633
  · exact u634
  · exact u635

def b4580 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 88 146 33 232 168 424), lower := (rows 97 7 292 88 146 33 64 128 256), losses := [] }

theorem u4580 : Upper (D 8) (R 8) [96,5,288,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4581 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 292 88 146 40 225 161 417), lower := (rows 97 7 292 88 146 40 64 128 256), losses := [] }

theorem u4581 : Upper (D 8) (R 8) [96,5,288,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4581 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4582 : Route 9 := (fun mask => (mask,id))

def c4582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4582 : Upper (D 8) (R 8) [96,5,288,80,130,128] 13 := by
  apply FastRouting.sound _ _ [96,5,288,80,130,128] 13 (by decide) (choices 1) [1,8,32] r4582 c4582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u636
  · exact u637
  · exact u638

def b4583 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 88 176 33 202 138 394), lower := (rows 97 7 292 88 176 33 64 128 256), losses := [] }

theorem u4583 : Upper (D 8) (R 8) [96,5,288,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4584 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 7 292 88 176 34 201 137 393), lower := (rows 97 7 292 88 176 34 64 128 256), losses := [] }

theorem u4584 : Upper (D 8) (R 8) [96,5,288,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4584 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4585 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 7 292 88 176 40 195 131 387), lower := (rows 97 7 292 88 176 40 64 128 256), losses := [] }

theorem u4585 : Upper (D 8) (R 8) [96,5,288,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4585 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4586 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 88 176 160 75 139 267), lower := (rows 97 7 292 88 176 160 64 128 256), losses := [] }

theorem u4586 : Upper (D 8) (R 8) [96,5,288,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4587 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 97 7 292 137 146 40 112 240 368), lower := (rows 97 7 292 137 146 40 64 128 256), losses := [] }

theorem u4587 : Upper (D 8) (R 8) [96,5,288,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4587 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4588 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 97 7 292 137 146 48 104 232 360), lower := (rows 97 7 292 137 146 48 64 128 256), losses := [] }

theorem u4588 : Upper (D 8) (R 8) [96,5,288,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4588 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4589 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 137 146 96 120 184 312), lower := (rows 97 7 292 137 146 96 64 128 256), losses := [] }

theorem u4589 : Upper (D 8) (R 8) [96,5,288,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4590 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 97 7 292 137 176 34 88 216 344), lower := (rows 97 7 292 137 176 34 64 128 256), losses := [] }

theorem u4590 : Upper (D 8) (R 8) [96,5,288,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4590 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4591 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 97 7 292 137 176 40 82 210 338), lower := (rows 97 7 292 137 176 40 64 128 256), losses := [] }

theorem u4591 : Upper (D 8) (R 8) [96,5,288,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4591 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4592 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 97 7 292 137 176 48 74 202 330), lower := (rows 97 7 292 137 176 48 64 128 256), losses := [] }

theorem u4592 : Upper (D 8) (R 8) [96,5,288,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4592 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4593 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 137 176 96 90 154 282), lower := (rows 97 7 292 137 176 96 64 128 256), losses := [] }

theorem u4593 : Upper (D 8) (R 8) [96,5,288,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4594 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 97 7 292 137 208 34 120 184 312), lower := (rows 97 7 292 137 208 34 64 128 256), losses := [] }

theorem u4594 : Upper (D 8) (R 8) [96,5,288,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4594 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4595 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 97 7 292 137 208 40 114 178 306), lower := (rows 97 7 292 137 208 40 64 128 256), losses := [] }

theorem u4595 : Upper (D 8) (R 8) [96,5,288,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4595 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4596 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 97 7 292 137 208 48 106 170 298), lower := (rows 97 7 292 137 208 48 64 128 256), losses := [] }

theorem u4596 : Upper (D 8) (R 8) [96,5,288,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4596 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4597 : PairBound 9 := { available := 88, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 138 176 33 88 216 344), lower := (rows 97 7 292 138 176 33 64 128 256), losses := [] }

theorem u4597 : Upper (D 8) (R 8) [96,5,288,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4598 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 7 292 138 176 40 81 209 337), lower := (rows 97 7 292 138 176 40 64 128 256), losses := [] }

theorem u4598 : Upper (D 8) (R 8) [96,5,288,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4598 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4599 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 7 292 138 176 48 73 201 329), lower := (rows 97 7 292 138 176 48 64 128 256), losses := [] }

theorem u4599 : Upper (D 8) (R 8) [96,5,288,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4599 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4600 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 138 176 96 89 153 281), lower := (rows 97 7 292 138 176 96 64 128 256), losses := [] }

theorem u4600 : Upper (D 8) (R 8) [96,5,288,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4601 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 138 208 33 120 184 312), lower := (rows 97 7 292 138 208 33 64 128 256), losses := [] }

theorem u4601 : Upper (D 8) (R 8) [96,5,288,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4602 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 7 292 138 208 40 113 177 305), lower := (rows 97 7 292 138 208 40 64 128 256), losses := [] }

theorem u4602 : Upper (D 8) (R 8) [96,5,288,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4602 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4603 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 7 292 138 208 48 105 169 297), lower := (rows 97 7 292 138 208 48 64 128 256), losses := [] }

theorem u4603 : Upper (D 8) (R 8) [96,5,288,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4603 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4604 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 168 208 33 90 154 282), lower := (rows 97 7 292 168 208 33 64 128 256), losses := [] }

theorem u4604 : Upper (D 8) (R 8) [96,5,288,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4605 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 7 292 168 208 34 89 153 281), lower := (rows 97 7 292 168 208 34 64 128 256), losses := [] }

theorem u4605 : Upper (D 8) (R 8) [96,5,288,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4605 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4606 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 7 292 168 208 40 83 147 275), lower := (rows 97 7 292 168 208 40 64 128 256), losses := [] }

theorem u4606 : Upper (D 8) (R 8) [96,5,288,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4606 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4607 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 7 292 168 208 48 75 139 267), lower := (rows 97 7 292 168 208 48 64 128 256), losses := [] }

theorem u4607 : Upper (D 8) (R 8) [96,5,288,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4607 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4608 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 26 56 33 224 224 480), lower := (rows 97 7 388 26 56 33 64 128 256), losses := [] }

theorem u4608 : Upper (D 8) (R 8) [96,5,384,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4609 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 26 56 96 225 161 417), lower := (rows 97 7 388 26 56 96 64 128 256), losses := [] }

theorem u4609 : Upper (D 8) (R 8) [96,5,384,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4610 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 26 56 160 97 225 353), lower := (rows 97 7 388 26 56 160 64 128 256), losses := [] }

theorem u4610 : Upper (D 8) (R 8) [96,5,384,18,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4611 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 42 88 33 240 176 432), lower := (rows 97 7 388 42 88 33 64 128 256), losses := [] }

theorem u4611 : Upper (D 8) (R 8) [96,5,384,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4612 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 388 42 88 48 225 161 417), lower := (rows 97 7 388 42 88 48 64 128 256), losses := [] }

theorem u4612 : Upper (D 8) (R 8) [96,5,384,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4612 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4613 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 42 88 160 113 177 305), lower := (rows 97 7 388 42 88 160 64 128 256), losses := [] }

theorem u4613 : Upper (D 8) (R 8) [96,5,384,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4614 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 97 7 388 42 145 40 112 240 368), lower := (rows 97 7 388 42 145 40 64 128 256), losses := [] }

theorem u4614 : Upper (D 8) (R 8) [96,5,384,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4614 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4615 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 97 7 388 42 145 48 104 232 360), lower := (rows 97 7 388 42 145 48 64 128 256), losses := [] }

theorem u4615 : Upper (D 8) (R 8) [96,5,384,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4615 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4616 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 42 145 96 120 184 312), lower := (rows 97 7 388 42 145 96 64 128 256), losses := [] }

theorem u4616 : Upper (D 8) (R 8) [96,5,384,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4617 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 42 176 33 88 216 344), lower := (rows 97 7 388 42 176 33 64 128 256), losses := [] }

theorem u4617 : Upper (D 8) (R 8) [96,5,384,34,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4618 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 7 388 42 176 40 81 209 337), lower := (rows 97 7 388 42 176 40 64 128 256), losses := [] }

theorem u4618 : Upper (D 8) (R 8) [96,5,384,34,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4618 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4619 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 7 388 42 176 48 73 201 329), lower := (rows 97 7 388 42 176 48 64 128 256), losses := [] }

theorem u4619 : Upper (D 8) (R 8) [96,5,384,34,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4619 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4619
end Delivery.IrregularNine14.P08
