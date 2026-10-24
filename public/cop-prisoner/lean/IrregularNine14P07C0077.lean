import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0005
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4620 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 290 70 104 146 48 65 129 385), lower := (rows 13 290 70 104 146 48 65 128 256), losses := [] }

theorem u4620 : Upper (D 7) (R 7) [12,288,66,96,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4620 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4621 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 70 104 146 48 192 129 257), lower := (rows 13 290 70 104 146 48 192 128 256), losses := [] }

theorem u4621 : Upper (D 7) (R 7) [12,288,66,96,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4621 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4622 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 13 290 70 104 146 160 65 145 273), lower := (rows 13 290 70 104 146 160 65 128 256), losses := [] }

theorem u4622 : Upper (D 7) (R 7) [12,288,66,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4623 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 70 104 146 160 80 129 257), lower := (rows 13 290 70 104 146 160 80 128 256), losses := [] }

theorem u4623 : Upper (D 7) (R 7) [12,288,66,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4623 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4624 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 13 290 70 138 81 33 80 160 416), lower := (rows 13 290 70 138 81 33 80 128 256), losses := [] }

theorem u4624 : Upper (D 7) (R 7) [12,288,66,130,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4624 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4625 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 153, targets := 32 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,5),(0,7),(3,5),(4,5)], upper := (rows 13 290 70 138 81 33 96 144 400), lower := (rows 13 290 70 138 81 33 96 128 256), losses := [] }

theorem u4625 : Upper (D 7) (R 7) [12,288,66,130,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4626 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 85, targets := 32 },{ cop := 4, region := 290, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(4,5)], upper := (rows 13 290 70 138 81 33 192 176 304), lower := (rows 13 290 70 138 81 33 192 128 256), losses := [] }

theorem u4626 : Upper (D 7) (R 7) [12,288,66,130,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4627 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 70 138 81 160 65 176 304), lower := (rows 13 290 70 138 81 160 65 128 256), losses := [] }

theorem u4627 : Upper (D 7) (R 7) [12,288,66,130,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4628 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 85, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 13 290 70 138 81 160 80 161 289), lower := (rows 13 290 70 138 81 160 80 128 256), losses := [] }

theorem u4628 : Upper (D 7) (R 7) [12,288,66,130,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4628 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4629 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 153, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 290 70 138 81 160 96 145 273), lower := (rows 13 290 70 138 81 160 96 128 256), losses := [] }

theorem u4629 : Upper (D 7) (R 7) [12,288,66,130,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4630 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 117, targets := 128 },{ cop := 4, region := 386, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 13 290 70 138 112 33 65 144 400), lower := (rows 13 290 70 138 112 33 65 128 256), losses := [] }

theorem u4630 : Upper (D 7) (R 7) [12,288,66,130,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4631 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0)], upper := (rows 13 290 70 138 112 33 80 129 385), lower := (rows 13 290 70 138 112 33 80 128 256), losses := [] }

theorem u4631 : Upper (D 7) (R 7) [12,288,66,130,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4631 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4632 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 0, region := 240, targets := 2 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(2,5),(4,1)], upper := (rows 13 290 70 138 112 33 192 145 273), lower := (rows 13 290 70 138 112 33 192 128 256), losses := [] }

theorem u4632 : Upper (D 7) (R 7) [12,288,66,130,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4633 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 70 138 112 160 65 145 273), lower := (rows 13 290 70 138 112 160 65 128 256), losses := [] }

theorem u4633 : Upper (D 7) (R 7) [12,288,66,130,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4634 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0)], upper := (rows 13 290 70 138 112 160 80 129 257), lower := (rows 13 290 70 138 112 160 80 128 256), losses := [] }

theorem u4634 : Upper (D 7) (R 7) [12,288,66,130,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4634 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4635 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 85, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(4,5)], upper := (rows 13 290 70 138 208 33 65 176 304), lower := (rows 13 290 70 138 208 33 65 128 256), losses := [] }

theorem u4635 : Upper (D 7) (R 7) [12,288,66,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4636 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 290 70 138 208 33 80 161 289), lower := (rows 13 290 70 138 208 33 80 128 256), losses := [] }

theorem u4636 : Upper (D 7) (R 7) [12,288,66,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4636 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4637 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 153, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 290 70 138 208 33 96 145 273), lower := (rows 13 290 70 138 208 33 96 128 256), losses := [] }

theorem u4637 : Upper (D 7) (R 7) [12,288,66,130,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4638 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 13 290 70 138 208 48 65 161 289), lower := (rows 13 290 70 138 208 48 65 128 256), losses := [] }

theorem u4638 : Upper (D 7) (R 7) [12,288,66,130,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4638 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4639 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 13 290 70 138 208 48 96 129 257), lower := (rows 13 290 70 138 208 48 96 128 256), losses := [] }

theorem u4639 : Upper (D 7) (R 7) [12,288,66,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4639 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4640 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 390, targets := 1 },{ cop := 4, region := 232, targets := 2 },{ cop := 4, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5),(3,1)], upper := (rows 13 290 70 152 19 96 65 160 416), lower := (rows 13 290 70 152 19 96 65 128 256), losses := [] }

theorem u4640 : Upper (D 7) (R 7) [12,288,66,144,3,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4641 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 153, targets := 96 }], pairs := [(0,5),(0,6),(3,5),(3,6)], upper := (rows 13 290 70 152 19 96 96 129 385), lower := (rows 13 290 70 152 19 96 96 128 256), losses := [] }

theorem u4641 : Upper (D 7) (R 7) [12,288,66,144,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4642 : Route 9 := (fun mask => (mask,id))

def c4642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4642 : Upper (D 7) (R 7) [12,288,66,144,3,64,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144,3,64,128] 13 (by decide) (choices 1) [1,32] r4642 c4642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u355
  · exact u356

def b4643 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 68, targets := 160 },{ cop := 6, region := 422, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(2,7)], upper := (rows 13 290 70 152 19 160 65 224 352), lower := (rows 13 290 70 152 19 160 65 128 256), losses := [] }

theorem u4643 : Upper (D 7) (R 7) [12,288,66,144,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4644 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 153, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 290 70 152 19 160 96 193 321), lower := (rows 13 290 70 152 19 160 96 128 256), losses := [] }

theorem u4644 : Upper (D 7) (R 7) [12,288,66,144,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4645 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 290 70 152 81 160 65 162 290), lower := (rows 13 290 70 152 81 160 65 128 256), losses := [] }

theorem u4645 : Upper (D 7) (R 7) [12,288,66,144,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4646 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 290 70 152 81 160 66 161 289), lower := (rows 13 290 70 152 81 160 66 128 256), losses := [] }

theorem u4646 : Upper (D 7) (R 7) [12,288,66,144,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4647 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 153, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 290 70 152 81 160 96 131 259), lower := (rows 13 290 70 152 81 160 96 128 256), losses := [] }

theorem u4647 : Upper (D 7) (R 7) [12,288,66,144,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4648 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 1 },{ cop := 0, region := 112, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 13 290 70 152 112 33 65 130 386), lower := (rows 13 290 70 152 112 33 65 128 256), losses := [] }

theorem u4648 : Upper (D 7) (R 7) [12,288,66,144,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4649 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 290 70 152 112 33 66 129 385), lower := (rows 13 290 70 152 112 33 66 128 256), losses := [] }

theorem u4649 : Upper (D 7) (R 7) [12,288,66,144,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4650 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 290, targets := 64 },{ cop := 0, region := 290, targets := 128 }], pairs := [(1,6),(1,7),(3,6),(4,1)], upper := (rows 13 290 70 152 112 33 192 131 259), lower := (rows 13 290 70 152 112 33 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 33 200 128 256), good := (rows 125 288 68 216 112 49 192 192 256) },{ target := 6, region := (rows 1 51 4 24 16 33 0 161 289), good := (rows 431 418 6 154 442 419 128 128 256) }] }

theorem u4650 : Upper (D 7) (R 7) [12,288,66,144,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4651 : Route 9 := (fun mask => (mask,id))

def c4651 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4651 : Upper (D 7) (R 7) [12,288,66,144,96,128,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144,96,128,1] 13 (by decide) (choices 1) [1,2] r4651 c4651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u357
  · exact u358

def b4652 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 290 70 152 112 160 66 129 257), lower := (rows 13 290 70 152 112 160 66 128 256), losses := [] }

theorem u4652 : Upper (D 7) (R 7) [12,288,66,144,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4653 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1)], upper := (rows 13 290 70 168 19 33 80 192 448), lower := (rows 13 290 70 168 19 33 80 128 256), losses := [] }

theorem u4653 : Upper (D 7) (R 7) [12,288,66,160,3,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4653 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4654 : Route 9 := (fun mask => (mask,id))

def c4654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4654 : Upper (D 7) (R 7) [12,288,66,160,3,1,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,3,1,128] 13 (by decide) (choices 1) [16,64] r4654 c4654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u359
  · exact u360

def b4655 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 232, targets := 2 },{ cop := 4, region := 68, targets := 32 },{ cop := 4, region := 68, targets := 128 }], pairs := [(2,5),(2,7),(3,1)], upper := (rows 13 290 70 168 19 48 65 192 448), lower := (rows 13 290 70 168 19 48 65 128 256), losses := [] }

theorem u4655 : Upper (D 7) (R 7) [12,288,66,160,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4655 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4656 : Route 9 := (fun mask => (mask,id))

def c4656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4656 : Upper (D 7) (R 7) [12,288,66,160,3,16,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,3,16,128] 13 (by decide) (choices 1) [1,64] r4656 c4656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u361
  · exact u362

def r4657 : Route 9 := (fun mask => (mask,id))

def c4657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4657 : Upper (D 7) (R 7) [12,288,66,160,3,64,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,3,64,1] 13 (by decide) (choices 1) [16] r4657 c4657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u363

def b4658 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1)], upper := (rows 13 290 70 168 19 96 80 129 385), lower := (rows 13 290 70 168 19 96 80 128 256), losses := [] }

theorem u4658 : Upper (D 7) (R 7) [12,288,66,160,3,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4658 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4659 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 40, targets := 3 },{ cop := 4, region := 196, targets := 32 }], pairs := [(0,1),(2,5),(3,0),(3,1)], upper := (rows 13 290 70 168 19 96 192 145 273), lower := (rows 13 290 70 168 19 96 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 216 16 253 216 144 272), good := (rows 109 288 109 232 505 104 232 232 256) }] }

theorem u4659 : Upper (D 7) (R 7) [12,288,66,160,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4660 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 290 70 168 81 33 66 144 400), lower := (rows 13 290 70 168 81 33 66 128 256), losses := [] }

theorem u4660 : Upper (D 7) (R 7) [12,288,66,160,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4661 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 13 290 70 168 81 33 80 130 386), lower := (rows 13 290 70 168 81 33 80 128 256), losses := [] }

theorem u4661 : Upper (D 7) (R 7) [12,288,66,160,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4661 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4662 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 4, region := 294, targets := 128 }], pairs := [(1,6),(1,7),(2,7),(3,6)], upper := (rows 13 290 70 168 81 33 192 146 274), lower := (rows 13 290 70 168 81 33 192 128 256), losses := [] }

theorem u4662 : Upper (D 7) (R 7) [12,288,66,160,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4663 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 13 290 70 168 81 48 65 130 386), lower := (rows 13 290 70 168 81 48 65 128 256), losses := [] }

theorem u4663 : Upper (D 7) (R 7) [12,288,66,160,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4663 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4664 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 13 290 70 168 81 48 66 129 385), lower := (rows 13 290 70 168 81 48 66 128 256), losses := [] }

theorem u4664 : Upper (D 7) (R 7) [12,288,66,160,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4664 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4665 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 4, region := 290, targets := 128 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 13 290 70 168 81 48 192 131 259), lower := (rows 13 290 70 168 81 48 192 128 256), losses := [] }

theorem u4665 : Upper (D 7) (R 7) [12,288,66,160,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4665 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4666 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 358, targets := 128 },{ cop := 4, region := 104, targets := 2 }], pairs := [(0,6),(1,7),(2,7),(3,1)], upper := (rows 13 290 70 168 145 96 65 146 274), lower := (rows 13 290 70 168 145 96 65 128 256), losses := [{ target := 6, region := (rows 5 42 4 42 85 32 0 165 293), good := (rows 415 426 415 426 401 442 401 128 256) }] }

theorem u4666 : Upper (D 7) (R 7) [12,288,66,160,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4667 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 102, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 290 70 168 145 96 66 145 273), lower := (rows 13 290 70 168 145 96 66 128 256), losses := [] }

theorem u4667 : Upper (D 7) (R 7) [12,288,66,160,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4668 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,7),(3,0),(3,1)], upper := (rows 13 290 70 168 145 96 80 131 259), lower := (rows 13 290 70 168 145 96 80 128 256), losses := [] }

theorem u4668 : Upper (D 7) (R 7) [12,288,66,160,129,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4668 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4669 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 144, targets := 33 }], pairs := [(2,5),(2,7),(4,0),(4,5)], upper := (rows 13 290 70 168 146 33 65 208 336), lower := (rows 13 290 70 168 146 33 65 128 256), losses := [{ target := 5, region := (rows 1 2 6 8 22 0 97 135 263), good := (rows 477 470 470 200 406 449 449 128 256) },{ target := 7, region := (rows 1 2 6 8 16 97 97 0 256), good := (rows 109 358 102 104 22 97 97 0 256) }] }

theorem u4669 : Upper (D 7) (R 7) [12,288,66,160,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4670 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 13 290 70 168 146 33 80 193 321), lower := (rows 13 290 70 168 146 33 80 128 256), losses := [] }

theorem u4670 : Upper (D 7) (R 7) [12,288,66,160,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4670 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4671 : Route 9 := (fun mask => (mask,id))

def c4671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4671 : Upper (D 7) (R 7) [12,288,66,160,130,64,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,130,64,1] 13 (by decide) (choices 1) [1,16] r4671 c4671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u364
  · exact u365

def b4672 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1)], upper := (rows 13 290 70 168 146 96 80 129 257), lower := (rows 13 290 70 168 146 96 80 128 256), losses := [] }

theorem u4672 : Upper (D 7) (R 7) [12,288,66,160,130,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4672 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4673 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 144, targets := 33 }], pairs := [(3,1),(4,0),(4,1),(4,5)], upper := (rows 13 290 70 168 208 33 65 146 274), lower := (rows 13 290 70 168 208 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 24 97 97 128 256), good := (rows 125 352 100 248 248 97 97 128 256) }] }

theorem u4673 : Upper (D 7) (R 7) [12,288,66,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4674 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 290 70 168 208 33 66 145 273), lower := (rows 13 290 70 168 208 33 66 128 256), losses := [] }

theorem u4674 : Upper (D 7) (R 7) [12,288,66,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4675 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 290 70 168 208 33 80 131 259), lower := (rows 13 290 70 168 208 33 80 128 256), losses := [] }

theorem u4675 : Upper (D 7) (R 7) [12,288,66,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4675 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4676 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(1,6),(4,6)], upper := (rows 13 290 70 200 19 33 80 160 416), lower := (rows 13 290 70 200 19 33 80 128 256), losses := [] }

theorem u4676 : Upper (D 7) (R 7) [12,288,66,192,3,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4676 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4677 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 153, targets := 32 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 290 70 200 19 33 96 144 400), lower := (rows 13 290 70 200 19 33 96 128 256), losses := [] }

theorem u4677 : Upper (D 7) (R 7) [12,288,66,192,3,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4678 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 70 200 19 33 192 176 304), lower := (rows 13 290 70 200 19 33 192 128 256), losses := [] }

theorem u4678 : Upper (D 7) (R 7) [12,288,66,192,3,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4679 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 68, targets := 160 }], pairs := [(1,6),(2,5),(2,7),(4,6)], upper := (rows 13 290 70 200 19 160 65 176 304), lower := (rows 13 290 70 200 19 160 65 128 256), losses := [] }

theorem u4679 : Upper (D 7) (R 7) [12,288,66,192,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4679
end Delivery.IrregularNine14.P07
