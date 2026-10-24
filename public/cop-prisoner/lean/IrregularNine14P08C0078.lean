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

def b4680 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 38 265 208 48 225 161 417), lower := (rows 97 14 38 265 208 48 64 128 256), losses := [] }

theorem u4680 : Upper (D 8) (R 8) [96,12,34,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4680 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4681 : Route 9 := (fun mask => (mask,id))

def c4681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4681 : Upper (D 8) (R 8) [96,12,34,257,192,128] 13 := by
  apply FastRouting.sound _ _ [96,12,34,257,192,128] 13 (by decide) (choices 1) [1,16,32] r4681 c4681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u641
  · exact u642
  · exact u643

def b4682 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 280 145 33 224 224 480), lower := (rows 97 14 38 280 145 33 64 128 256), losses := [] }

theorem u4682 : Upper (D 8) (R 8) [96,12,34,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4683 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 280 145 96 225 161 417), lower := (rows 97 14 38 280 145 96 64 128 256), losses := [] }

theorem u4683 : Upper (D 8) (R 8) [96,12,34,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4684 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 280 145 160 97 225 353), lower := (rows 97 14 38 280 145 160 64 128 256), losses := [] }

theorem u4684 : Upper (D 8) (R 8) [96,12,34,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4685 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 280 176 33 193 193 449), lower := (rows 97 14 38 280 176 33 64 128 256), losses := [] }

theorem u4685 : Upper (D 8) (R 8) [96,12,34,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4686 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 280 176 96 193 129 385), lower := (rows 97 14 38 280 176 96 64 128 256), losses := [] }

theorem u4686 : Upper (D 8) (R 8) [96,12,34,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4687 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 280 176 160 65 193 321), lower := (rows 97 14 38 280 176 160 64 128 256), losses := [] }

theorem u4687 : Upper (D 8) (R 8) [96,12,34,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4688 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 280 208 33 225 161 417), lower := (rows 97 14 38 280 208 33 64 128 256), losses := [] }

theorem u4688 : Upper (D 8) (R 8) [96,12,34,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4689 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 280 208 160 97 161 289), lower := (rows 97 14 38 280 208 160 64 128 256), losses := [] }

theorem u4689 : Upper (D 8) (R 8) [96,12,34,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4690 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 14 52 137 273 34 224 224 480), lower := (rows 97 14 52 137 273 34 64 128 256), losses := [] }

theorem u4690 : Upper (D 8) (R 8) [96,12,48,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4690 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4691 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 137 273 96 226 162 418), lower := (rows 97 14 52 137 273 96 64 128 256), losses := [] }

theorem u4691 : Upper (D 8) (R 8) [96,12,48,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4692 : Route 9 := (fun mask => (mask,id))

def c4692 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4692 : Upper (D 8) (R 8) [96,12,48,129,257,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,257,128] 13 (by decide) (choices 1) [2,32] r4692 c4692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u644
  · exact u645

def b4693 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 274 33 224 224 480), lower := (rows 97 14 52 137 274 33 64 128 256), losses := [] }

theorem u4693 : Upper (D 8) (R 8) [96,12,48,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4694 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 137 274 96 225 161 417), lower := (rows 97 14 52 137 274 96 64 128 256), losses := [] }

theorem u4694 : Upper (D 8) (R 8) [96,12,48,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4695 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 274 160 97 225 353), lower := (rows 97 14 52 137 274 160 64 128 256), losses := [] }

theorem u4695 : Upper (D 8) (R 8) [96,12,48,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4696 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 336 33 226 162 418), lower := (rows 97 14 52 137 336 33 64 128 256), losses := [] }

theorem u4696 : Upper (D 8) (R 8) [96,12,48,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4697 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 52 137 336 34 225 161 417), lower := (rows 97 14 52 137 336 34 64 128 256), losses := [] }

theorem u4697 : Upper (D 8) (R 8) [96,12,48,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4697 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4698 : Route 9 := (fun mask => (mask,id))

def c4698 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4698 : Upper (D 8) (R 8) [96,12,48,129,320,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,320,128] 13 (by decide) (choices 1) [1,2,32] r4698 c4698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u646
  · exact u647
  · exact u648

def b4699 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 52 138 273 33 224 224 480), lower := (rows 97 14 52 138 273 33 64 128 256), losses := [] }

theorem u4699 : Upper (D 8) (R 8) [96,12,48,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4700 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 138 273 96 225 161 417), lower := (rows 97 14 52 138 273 96 64 128 256), losses := [] }

theorem u4700 : Upper (D 8) (R 8) [96,12,48,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4701 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 138 273 160 97 225 353), lower := (rows 97 14 52 138 273 160 64 128 256), losses := [] }

theorem u4701 : Upper (D 8) (R 8) [96,12,48,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4702 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 138 336 33 225 161 417), lower := (rows 97 14 52 138 336 33 64 128 256), losses := [] }

theorem u4702 : Upper (D 8) (R 8) [96,12,48,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4703 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 138 336 160 97 161 289), lower := (rows 97 14 52 138 336 160 64 128 256), losses := [] }

theorem u4703 : Upper (D 8) (R 8) [96,12,48,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4704 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 52 168 273 33 194 194 450), lower := (rows 97 14 52 168 273 33 64 128 256), losses := [] }

theorem u4704 : Upper (D 8) (R 8) [96,12,48,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4705 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 14 52 168 273 34 193 193 449), lower := (rows 97 14 52 168 273 34 64 128 256), losses := [] }

theorem u4705 : Upper (D 8) (R 8) [96,12,48,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4705 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4706 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 168 273 96 195 131 387), lower := (rows 97 14 52 168 273 96 64 128 256), losses := [] }

theorem u4706 : Upper (D 8) (R 8) [96,12,48,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4707 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 168 273 160 67 195 323), lower := (rows 97 14 52 168 273 160 64 128 256), losses := [] }

theorem u4707 : Upper (D 8) (R 8) [96,12,48,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4708 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 168 274 33 193 193 449), lower := (rows 97 14 52 168 274 33 64 128 256), losses := [] }

theorem u4708 : Upper (D 8) (R 8) [96,12,48,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4709 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 168 274 96 193 129 385), lower := (rows 97 14 52 168 274 96 64 128 256), losses := [] }

theorem u4709 : Upper (D 8) (R 8) [96,12,48,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4710 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 168 274 160 65 193 321), lower := (rows 97 14 52 168 274 160 64 128 256), losses := [] }

theorem u4710 : Upper (D 8) (R 8) [96,12,48,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4711 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 168 336 33 195 131 387), lower := (rows 97 14 52 168 336 33 64 128 256), losses := [] }

theorem u4711 : Upper (D 8) (R 8) [96,12,48,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4712 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 52 168 336 34 193 129 385), lower := (rows 97 14 52 168 336 34 64 128 256), losses := [] }

theorem u4712 : Upper (D 8) (R 8) [96,12,48,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4712 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4713 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 168 336 160 67 131 259), lower := (rows 97 14 52 168 336 160 64 128 256), losses := [] }

theorem u4713 : Upper (D 8) (R 8) [96,12,48,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4714 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 52 200 273 33 226 162 418), lower := (rows 97 14 52 200 273 33 64 128 256), losses := [] }

theorem u4714 : Upper (D 8) (R 8) [96,12,48,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4714 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4715 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 52 200 273 34 225 161 417), lower := (rows 97 14 52 200 273 34 64 128 256), losses := [] }

theorem u4715 : Upper (D 8) (R 8) [96,12,48,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4715 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4716 : Route 9 := (fun mask => (mask,id))

def c4716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4716 : Upper (D 8) (R 8) [96,12,48,192,257,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,257,128] 13 (by decide) (choices 1) [1,2,32] r4716 c4716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u649
  · exact u650
  · exact u651

def b4717 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 200 274 33 225 161 417), lower := (rows 97 14 52 200 274 33 64 128 256), losses := [] }

theorem u4717 : Upper (D 8) (R 8) [96,12,48,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4718 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 200 274 160 97 161 289), lower := (rows 97 14 52 200 274 160 64 128 256), losses := [] }

theorem u4718 : Upper (D 8) (R 8) [96,12,48,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4719 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 14 52 265 145 34 224 224 480), lower := (rows 97 14 52 265 145 34 64 128 256), losses := [] }

theorem u4719 : Upper (D 8) (R 8) [96,12,48,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4719 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4720 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 265 145 96 226 162 418), lower := (rows 97 14 52 265 145 96 64 128 256), losses := [] }

theorem u4720 : Upper (D 8) (R 8) [96,12,48,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4721 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 265 145 160 98 226 354), lower := (rows 97 14 52 265 145 160 64 128 256), losses := [] }

theorem u4721 : Upper (D 8) (R 8) [96,12,48,257,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4722 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 265 146 33 224 224 480), lower := (rows 97 14 52 265 146 33 64 128 256), losses := [] }

theorem u4722 : Upper (D 8) (R 8) [96,12,48,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4723 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 265 146 96 225 161 417), lower := (rows 97 14 52 265 146 96 64 128 256), losses := [] }

theorem u4723 : Upper (D 8) (R 8) [96,12,48,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4724 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 265 146 160 97 225 353), lower := (rows 97 14 52 265 146 160 64 128 256), losses := [] }

theorem u4724 : Upper (D 8) (R 8) [96,12,48,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4725 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 265 208 33 226 162 418), lower := (rows 97 14 52 265 208 33 64 128 256), losses := [] }

theorem u4725 : Upper (D 8) (R 8) [96,12,48,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4726 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 52 265 208 34 225 161 417), lower := (rows 97 14 52 265 208 34 64 128 256), losses := [] }

theorem u4726 : Upper (D 8) (R 8) [96,12,48,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4726 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4727 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 265 208 160 99 163 291), lower := (rows 97 14 52 265 208 160 64 128 256), losses := [] }

theorem u4727 : Upper (D 8) (R 8) [96,12,48,257,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4728 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 52 266 145 33 224 224 480), lower := (rows 97 14 52 266 145 33 64 128 256), losses := [] }

theorem u4728 : Upper (D 8) (R 8) [96,12,48,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4729 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 266 145 96 225 161 417), lower := (rows 97 14 52 266 145 96 64 128 256), losses := [] }

theorem u4729 : Upper (D 8) (R 8) [96,12,48,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4730 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 266 145 160 97 225 353), lower := (rows 97 14 52 266 145 160 64 128 256), losses := [] }

theorem u4730 : Upper (D 8) (R 8) [96,12,48,258,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4731 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 266 208 33 225 161 417), lower := (rows 97 14 52 266 208 33 64 128 256), losses := [] }

theorem u4731 : Upper (D 8) (R 8) [96,12,48,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4732 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 266 208 160 97 161 289), lower := (rows 97 14 52 266 208 160 64 128 256), losses := [] }

theorem u4732 : Upper (D 8) (R 8) [96,12,48,258,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4733 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 52 296 145 33 194 194 450), lower := (rows 97 14 52 296 145 33 64 128 256), losses := [] }

theorem u4733 : Upper (D 8) (R 8) [96,12,48,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4734 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 14 52 296 145 34 193 193 449), lower := (rows 97 14 52 296 145 34 64 128 256), losses := [] }

theorem u4734 : Upper (D 8) (R 8) [96,12,48,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4734 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4735 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 296 145 96 195 131 387), lower := (rows 97 14 52 296 145 96 64 128 256), losses := [] }

theorem u4735 : Upper (D 8) (R 8) [96,12,48,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4736 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 296 145 160 67 195 323), lower := (rows 97 14 52 296 145 160 64 128 256), losses := [] }

theorem u4736 : Upper (D 8) (R 8) [96,12,48,288,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4737 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 296 146 33 193 193 449), lower := (rows 97 14 52 296 146 33 64 128 256), losses := [] }

theorem u4737 : Upper (D 8) (R 8) [96,12,48,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4738 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 296 146 96 193 129 385), lower := (rows 97 14 52 296 146 96 64 128 256), losses := [] }

theorem u4738 : Upper (D 8) (R 8) [96,12,48,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4739 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 296 146 160 65 193 321), lower := (rows 97 14 52 296 146 160 64 128 256), losses := [] }

theorem u4739 : Upper (D 8) (R 8) [96,12,48,288,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4739
end Delivery.IrregularNine14.P08
