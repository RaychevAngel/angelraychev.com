import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0010
import IrregularNine14P08C0011

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4740 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 296 208 33 195 131 387), lower := (rows 97 14 52 296 208 33 64 128 256), losses := [] }

theorem u4740 : Upper (D 8) (R 8) [96,12,48,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4741 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 52 296 208 34 193 129 385), lower := (rows 97 14 52 296 208 34 64 128 256), losses := [] }

theorem u4741 : Upper (D 8) (R 8) [96,12,48,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4741 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4742 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 296 208 160 67 131 259), lower := (rows 97 14 52 296 208 160 64 128 256), losses := [] }

theorem u4742 : Upper (D 8) (R 8) [96,12,48,288,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4743 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 52 328 145 33 226 162 418), lower := (rows 97 14 52 328 145 33 64 128 256), losses := [] }

theorem u4743 : Upper (D 8) (R 8) [96,12,48,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4744 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 52 328 145 34 225 161 417), lower := (rows 97 14 52 328 145 34 64 128 256), losses := [] }

theorem u4744 : Upper (D 8) (R 8) [96,12,48,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4744 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4745 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 328 145 160 99 163 291), lower := (rows 97 14 52 328 145 160 64 128 256), losses := [] }

theorem u4745 : Upper (D 8) (R 8) [96,12,48,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4746 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 328 146 33 225 161 417), lower := (rows 97 14 52 328 146 33 64 128 256), losses := [] }

theorem u4746 : Upper (D 8) (R 8) [96,12,48,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4747 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 328 146 160 97 161 289), lower := (rows 97 14 52 328 146 160 64 128 256), losses := [] }

theorem u4747 : Upper (D 8) (R 8) [96,12,48,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4748 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 97 14 84 137 273 34 224 160 416), lower := (rows 97 14 84 137 273 34 64 128 256), losses := [] }

theorem u4748 : Upper (D 8) (R 8) [96,12,80,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4748 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4749 : Route 9 := (fun mask => (mask,id))

def c4749 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4749 : Upper (D 8) (R 8) [96,12,80,129,257,128] 13 := by
  apply FastRouting.sound _ _ [96,12,80,129,257,128] 13 (by decide) (choices 1) [2,32] r4749 c4749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u652
  · exact u653

def b4750 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 137 304 33 226 162 418), lower := (rows 97 14 84 137 304 33 64 128 256), losses := [] }

theorem u4750 : Upper (D 8) (R 8) [96,12,80,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4751 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 84 137 304 34 225 161 417), lower := (rows 97 14 84 137 304 34 64 128 256), losses := [] }

theorem u4751 : Upper (D 8) (R 8) [96,12,80,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4751 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4752 : Route 9 := (fun mask => (mask,id))

def c4752 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4752 : Upper (D 8) (R 8) [96,12,80,129,288,128] 13 := by
  apply FastRouting.sound _ _ [96,12,80,129,288,128] 13 (by decide) (choices 1) [1,2,32] r4752 c4752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u654
  · exact u655
  · exact u656

def b4753 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 168 273 33 226 162 418), lower := (rows 97 14 84 168 273 33 64 128 256), losses := [] }

theorem u4753 : Upper (D 8) (R 8) [96,12,80,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4754 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 84 168 273 34 225 161 417), lower := (rows 97 14 84 168 273 34 64 128 256), losses := [] }

theorem u4754 : Upper (D 8) (R 8) [96,12,80,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4754 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4755 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 168 273 160 99 163 291), lower := (rows 97 14 84 168 273 160 64 128 256), losses := [] }

theorem u4755 : Upper (D 8) (R 8) [96,12,80,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4756 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 168 304 33 195 131 387), lower := (rows 97 14 84 168 304 33 64 128 256), losses := [] }

theorem u4756 : Upper (D 8) (R 8) [96,12,80,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4757 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 84 168 304 34 193 129 385), lower := (rows 97 14 84 168 304 34 64 128 256), losses := [] }

theorem u4757 : Upper (D 8) (R 8) [96,12,80,160,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4757 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4758 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 168 304 160 67 131 259), lower := (rows 97 14 84 168 304 160 64 128 256), losses := [] }

theorem u4758 : Upper (D 8) (R 8) [96,12,80,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4759 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 97 14 84 265 145 34 224 160 416), lower := (rows 97 14 84 265 145 34 64 128 256), losses := [] }

theorem u4759 : Upper (D 8) (R 8) [96,12,80,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4759 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4760 : Route 9 := (fun mask => (mask,id))

def c4760 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4760 : Upper (D 8) (R 8) [96,12,80,257,129,128] 13 := by
  apply FastRouting.sound _ _ [96,12,80,257,129,128] 13 (by decide) (choices 1) [2,32] r4760 c4760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u657
  · exact u658

def b4761 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 265 176 33 226 162 418), lower := (rows 97 14 84 265 176 33 64 128 256), losses := [] }

theorem u4761 : Upper (D 8) (R 8) [96,12,80,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4762 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 84 265 176 34 225 161 417), lower := (rows 97 14 84 265 176 34 64 128 256), losses := [] }

theorem u4762 : Upper (D 8) (R 8) [96,12,80,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4762 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4763 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 265 176 160 99 163 291), lower := (rows 97 14 84 265 176 160 64 128 256), losses := [] }

theorem u4763 : Upper (D 8) (R 8) [96,12,80,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4764 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 296 145 33 226 162 418), lower := (rows 97 14 84 296 145 33 64 128 256), losses := [] }

theorem u4764 : Upper (D 8) (R 8) [96,12,80,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4765 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 84 296 145 34 225 161 417), lower := (rows 97 14 84 296 145 34 64 128 256), losses := [] }

theorem u4765 : Upper (D 8) (R 8) [96,12,80,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4765 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4766 : Route 9 := (fun mask => (mask,id))

def c4766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4766 : Upper (D 8) (R 8) [96,12,80,288,129,128] 13 := by
  apply FastRouting.sound _ _ [96,12,80,288,129,128] 13 (by decide) (choices 1) [1,2,32] r4766 c4766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u659
  · exact u660
  · exact u661

def b4767 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 296 176 33 195 131 387), lower := (rows 97 14 84 296 176 33 64 128 256), losses := [] }

theorem u4767 : Upper (D 8) (R 8) [96,12,80,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4768 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 84 296 176 34 193 129 385), lower := (rows 97 14 84 296 176 34 64 128 256), losses := [] }

theorem u4768 : Upper (D 8) (R 8) [96,12,80,288,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4768 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4769 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 296 176 160 67 131 259), lower := (rows 97 14 84 296 176 160 64 128 256), losses := [] }

theorem u4769 : Upper (D 8) (R 8) [96,12,80,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4770 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 133 280 50 33 224 224 480), lower := (rows 97 14 133 280 50 33 64 128 256), losses := [] }

theorem u4770 : Upper (D 8) (R 8) [96,12,129,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4771 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 133 280 50 96 225 161 417), lower := (rows 97 14 133 280 50 96 64 128 256), losses := [] }

theorem u4771 : Upper (D 8) (R 8) [96,12,129,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4771 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4772 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 280 50 160 97 225 353), lower := (rows 97 14 133 280 50 160 64 128 256), losses := [] }

theorem u4772 : Upper (D 8) (R 8) [96,12,129,272,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4773 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 133 296 50 33 208 208 464), lower := (rows 97 14 133 296 50 33 64 128 256), losses := [] }

theorem u4773 : Upper (D 8) (R 8) [96,12,129,288,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4774 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 14 133 296 50 48 193 193 449), lower := (rows 97 14 133 296 50 48 64 128 256), losses := [] }

theorem u4774 : Upper (D 8) (R 8) [96,12,129,288,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4774 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4775 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 133 296 50 96 209 145 401), lower := (rows 97 14 133 296 50 96 64 128 256), losses := [] }

theorem u4775 : Upper (D 8) (R 8) [96,12,129,288,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4776 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 296 50 160 81 209 337), lower := (rows 97 14 133 296 50 160 64 128 256), losses := [] }

theorem u4776 : Upper (D 8) (R 8) [96,12,129,288,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4777 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 296 82 33 240 176 432), lower := (rows 97 14 133 296 82 33 64 128 256), losses := [] }

theorem u4777 : Upper (D 8) (R 8) [96,12,129,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4778 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 133 296 82 48 225 161 417), lower := (rows 97 14 133 296 82 48 64 128 256), losses := [] }

theorem u4778 : Upper (D 8) (R 8) [96,12,129,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4778 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4779 : Route 9 := (fun mask => (mask,id))

def c4779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4779 : Upper (D 8) (R 8) [96,12,129,288,66,128] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,66,128] 13 (by decide) (choices 1) [1,16,32] r4779 c4779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u662
  · exact u663
  · exact u664

def b4780 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 133 296 176 33 82 210 338), lower := (rows 97 14 133 296 176 33 64 128 256), losses := [] }

theorem u4780 : Upper (D 8) (R 8) [96,12,129,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4781 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 14 133 296 176 34 81 209 337), lower := (rows 97 14 133 296 176 34 64 128 256), losses := [] }

theorem u4781 : Upper (D 8) (R 8) [96,12,129,288,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4781 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4782 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 14 133 296 176 48 67 195 323), lower := (rows 97 14 133 296 176 48 64 128 256), losses := [] }

theorem u4782 : Upper (D 8) (R 8) [96,12,129,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4782 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4783 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 133 296 176 96 83 147 275), lower := (rows 97 14 133 296 176 96 64 128 256), losses := [] }

theorem u4783 : Upper (D 8) (R 8) [96,12,129,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4784 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 296 208 33 114 178 306), lower := (rows 97 14 133 296 208 33 64 128 256), losses := [] }

theorem u4784 : Upper (D 8) (R 8) [96,12,129,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4785 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 14 133 296 208 34 113 177 305), lower := (rows 97 14 133 296 208 34 64 128 256), losses := [] }

theorem u4785 : Upper (D 8) (R 8) [96,12,129,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4785 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4786 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 14 133 296 208 48 99 163 291), lower := (rows 97 14 133 296 208 48 64 128 256), losses := [] }

theorem u4786 : Upper (D 8) (R 8) [96,12,129,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4786 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4787 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 328 50 33 240 176 432), lower := (rows 97 14 133 328 50 33 64 128 256), losses := [] }

theorem u4787 : Upper (D 8) (R 8) [96,12,129,320,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4788 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 133 328 50 48 225 161 417), lower := (rows 97 14 133 328 50 48 64 128 256), losses := [] }

theorem u4788 : Upper (D 8) (R 8) [96,12,129,320,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4788 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4789 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 328 50 160 113 177 305), lower := (rows 97 14 133 328 50 160 64 128 256), losses := [] }

theorem u4789 : Upper (D 8) (R 8) [96,12,129,320,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4790 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 133 328 176 33 114 178 306), lower := (rows 97 14 133 328 176 33 64 128 256), losses := [] }

theorem u4790 : Upper (D 8) (R 8) [96,12,129,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4791 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 14 133 328 176 34 113 177 305), lower := (rows 97 14 133 328 176 34 64 128 256), losses := [] }

theorem u4791 : Upper (D 8) (R 8) [96,12,129,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4791 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4792 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 14 133 328 176 48 99 163 291), lower := (rows 97 14 133 328 176 48 64 128 256), losses := [] }

theorem u4792 : Upper (D 8) (R 8) [96,12,129,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4792 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4793 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 148 265 50 33 224 224 480), lower := (rows 97 14 148 265 50 33 64 128 256), losses := [] }

theorem u4793 : Upper (D 8) (R 8) [96,12,144,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4794 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 148 265 50 96 225 161 417), lower := (rows 97 14 148 265 50 96 64 128 256), losses := [] }

theorem u4794 : Upper (D 8) (R 8) [96,12,144,257,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4795 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 265 50 160 97 225 353), lower := (rows 97 14 148 265 50 160 64 128 256), losses := [] }

theorem u4795 : Upper (D 8) (R 8) [96,12,144,257,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4796 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 296 50 33 193 193 449), lower := (rows 97 14 148 296 50 33 64 128 256), losses := [] }

theorem u4796 : Upper (D 8) (R 8) [96,12,144,288,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4797 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 148 296 50 96 193 129 385), lower := (rows 97 14 148 296 50 96 64 128 256), losses := [] }

theorem u4797 : Upper (D 8) (R 8) [96,12,144,288,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4798 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 296 50 160 65 193 321), lower := (rows 97 14 148 296 50 160 64 128 256), losses := [] }

theorem u4798 : Upper (D 8) (R 8) [96,12,144,288,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4799 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 328 50 33 225 161 417), lower := (rows 97 14 148 328 50 33 64 128 256), losses := [] }

theorem u4799 : Upper (D 8) (R 8) [96,12,144,320,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4799
end Delivery.IrregularNine14.P08
