import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0014

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6720 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 321 7 164 74 145 48 104 168 296), lower := (rows 321 7 164 74 145 48 64 128 256), losses := [] }

theorem u6720 : Upper (D 8) (R 8) [320,5,160,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6720 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6721 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 321 7 164 88 145 34 104 168 296), lower := (rows 321 7 164 88 145 34 64 128 256), losses := [] }

theorem u6721 : Upper (D 8) (R 8) [320,5,160,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6721 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6722 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 321 7 164 88 145 40 98 162 290), lower := (rows 321 7 164 88 145 40 64 128 256), losses := [] }

theorem u6722 : Upper (D 8) (R 8) [320,5,160,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6722 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6723 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 321 7 164 104 145 34 120 184 312), lower := (rows 321 7 164 104 145 34 64 128 256), losses := [] }

theorem u6723 : Upper (D 8) (R 8) [320,5,160,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6723 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6724 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 321 7 164 104 145 40 114 178 306), lower := (rows 321 7 164 104 145 40 64 128 256), losses := [] }

theorem u6724 : Upper (D 8) (R 8) [320,5,160,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6724 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6725 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 321 7 164 104 145 48 106 170 298), lower := (rows 321 7 164 104 145 48 64 128 256), losses := [] }

theorem u6725 : Upper (D 8) (R 8) [320,5,160,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6725 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6726 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 321 7 164 104 152 33 114 178 306), lower := (rows 321 7 164 104 152 33 64 128 256), losses := [] }

theorem u6726 : Upper (D 8) (R 8) [320,5,160,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6727 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 7 164 104 152 34 113 177 305), lower := (rows 321 7 164 104 152 34 64 128 256), losses := [] }

theorem u6727 : Upper (D 8) (R 8) [320,5,160,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6727 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6728 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 7 164 104 152 48 99 163 291), lower := (rows 321 7 164 104 152 48 64 128 256), losses := [] }

theorem u6728 : Upper (D 8) (R 8) [320,5,160,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6728 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6729 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 150, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 22 41 145 96 224 160 416), lower := (rows 321 14 22 41 145 96 64 128 256), losses := [] }

theorem u6729 : Upper (D 8) (R 8) [320,12,18,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6730 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 46, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 22 41 145 160 96 224 352), lower := (rows 321 14 22 41 145 160 64 128 256), losses := [] }

theorem u6730 : Upper (D 8) (R 8) [320,12,18,33,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6731 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 22 41 176 33 224 224 480), lower := (rows 321 14 22 41 176 33 64 128 256), losses := [] }

theorem u6731 : Upper (D 8) (R 8) [320,12,18,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6732 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 150, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 22 41 176 96 225 161 417), lower := (rows 321 14 22 41 176 96 64 128 256), losses := [] }

theorem u6732 : Upper (D 8) (R 8) [320,12,18,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6733 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 22 41 176 160 97 225 353), lower := (rows 321 14 22 41 176 160 64 128 256), losses := [] }

theorem u6733 : Upper (D 8) (R 8) [320,12,18,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6734 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 321 14 37 56 145 34 224 224 480), lower := (rows 321 14 37 56 145 34 64 128 256), losses := [] }

theorem u6734 : Upper (D 8) (R 8) [320,12,33,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6734 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6735 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 154, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 56 145 96 226 162 418), lower := (rows 321 14 37 56 145 96 64 128 256), losses := [] }

theorem u6735 : Upper (D 8) (R 8) [320,12,33,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6736 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 56 145 160 98 226 354), lower := (rows 321 14 37 56 145 160 64 128 256), losses := [] }

theorem u6736 : Upper (D 8) (R 8) [320,12,33,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6737 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 56 146 33 224 224 480), lower := (rows 321 14 37 56 146 33 64 128 256), losses := [] }

theorem u6737 : Upper (D 8) (R 8) [320,12,33,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6738 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 154, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 56 146 96 225 161 417), lower := (rows 321 14 37 56 146 96 64 128 256), losses := [] }

theorem u6738 : Upper (D 8) (R 8) [320,12,33,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6739 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 56 146 160 97 225 353), lower := (rows 321 14 37 56 146 160 64 128 256), losses := [] }

theorem u6739 : Upper (D 8) (R 8) [320,12,33,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6740 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 56 208 33 226 162 418), lower := (rows 321 14 37 56 208 33 64 128 256), losses := [] }

theorem u6740 : Upper (D 8) (R 8) [320,12,33,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6741 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 37 56 208 34 225 161 417), lower := (rows 321 14 37 56 208 34 64 128 256), losses := [] }

theorem u6741 : Upper (D 8) (R 8) [320,12,33,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6741 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6742 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 56 208 160 99 163 291), lower := (rows 321 14 37 56 208 160 64 128 256), losses := [] }

theorem u6742 : Upper (D 8) (R 8) [320,12,33,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6743 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 321 14 37 88 145 34 224 160 416), lower := (rows 321 14 37 88 145 34 64 128 256), losses := [] }

theorem u6743 : Upper (D 8) (R 8) [320,12,33,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6743 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6744 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 321 14 37 88 145 160 98 162 290), lower := (rows 321 14 37 88 145 160 64 128 256), losses := [] }

theorem u6744 : Upper (D 8) (R 8) [320,12,33,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6745 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 88 176 33 226 162 418), lower := (rows 321 14 37 88 176 33 64 128 256), losses := [] }

theorem u6745 : Upper (D 8) (R 8) [320,12,33,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6746 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 37 88 176 34 225 161 417), lower := (rows 321 14 37 88 176 34 64 128 256), losses := [] }

theorem u6746 : Upper (D 8) (R 8) [320,12,33,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6746 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6747 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 88 176 160 99 163 291), lower := (rows 321 14 37 88 176 160 64 128 256), losses := [] }

theorem u6747 : Upper (D 8) (R 8) [320,12,33,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6748 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 321 14 37 104 145 34 240 176 432), lower := (rows 321 14 37 104 145 34 64 128 256), losses := [] }

theorem u6748 : Upper (D 8) (R 8) [320,12,33,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6748 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6749 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 321 14 37 104 145 48 226 162 418), lower := (rows 321 14 37 104 145 48 64 128 256), losses := [] }

theorem u6749 : Upper (D 8) (R 8) [320,12,33,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6749 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6750 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 321 14 37 104 145 160 114 178 306), lower := (rows 321 14 37 104 145 160 64 128 256), losses := [] }

theorem u6750 : Upper (D 8) (R 8) [320,12,33,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6751 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 46, targets := 128 }], pairs := [(1,7)], upper := (rows 321 14 37 104 146 33 240 176 432), lower := (rows 321 14 37 104 146 33 64 128 256), losses := [] }

theorem u6751 : Upper (D 8) (R 8) [320,12,33,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6752 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 37 104 146 48 225 161 417), lower := (rows 321 14 37 104 146 48 64 128 256), losses := [] }

theorem u6752 : Upper (D 8) (R 8) [320,12,33,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6752 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6753 : Route 9 := (fun mask => (mask,id))

def c6753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6753 : Upper (D 8) (R 8) [320,12,33,96,130,128] 13 := by
  apply FastRouting.sound _ _ [320,12,33,96,130,128] 13 (by decide) (choices 1) [1,16,32] r6753 c6753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u848
  · exact u849
  · exact u850

def b6754 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 46, targets := 128 }], pairs := [(1,7)], upper := (rows 321 14 37 104 176 33 210 146 402), lower := (rows 321 14 37 104 176 33 64 128 256), losses := [] }

theorem u6754 : Upper (D 8) (R 8) [320,12,33,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6755 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 321 14 37 104 176 34 209 145 401), lower := (rows 321 14 37 104 176 34 64 128 256), losses := [] }

theorem u6755 : Upper (D 8) (R 8) [320,12,33,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6755 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6756 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 321 14 37 104 176 48 195 131 387), lower := (rows 321 14 37 104 176 48 64 128 256), losses := [] }

theorem u6756 : Upper (D 8) (R 8) [320,12,33,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6756 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6757 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 104 176 160 83 147 275), lower := (rows 321 14 37 104 176 160 64 128 256), losses := [] }

theorem u6757 : Upper (D 8) (R 8) [320,12,33,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6758 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 138 112 33 240 176 432), lower := (rows 321 14 37 138 112 33 64 128 256), losses := [] }

theorem u6758 : Upper (D 8) (R 8) [320,12,33,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6759 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 37 138 112 48 225 161 417), lower := (rows 321 14 37 138 112 48 64 128 256), losses := [] }

theorem u6759 : Upper (D 8) (R 8) [320,12,33,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6759 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6760 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 138 112 160 113 177 305), lower := (rows 321 14 37 138 112 160 64 128 256), losses := [] }

theorem u6760 : Upper (D 8) (R 8) [320,12,33,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6761 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 152 50 33 224 224 480), lower := (rows 321 14 37 152 50 33 64 128 256), losses := [] }

theorem u6761 : Upper (D 8) (R 8) [320,12,33,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6762 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 154, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 152 50 96 225 161 417), lower := (rows 321 14 37 152 50 96 64 128 256), losses := [] }

theorem u6762 : Upper (D 8) (R 8) [320,12,33,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6762 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6763 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 152 50 160 97 225 353), lower := (rows 321 14 37 152 50 160 64 128 256), losses := [] }

theorem u6763 : Upper (D 8) (R 8) [320,12,33,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6764 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 152 112 33 226 162 418), lower := (rows 321 14 37 152 112 33 64 128 256), losses := [] }

theorem u6764 : Upper (D 8) (R 8) [320,12,33,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6765 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 37 152 112 34 225 161 417), lower := (rows 321 14 37 152 112 34 64 128 256), losses := [] }

theorem u6765 : Upper (D 8) (R 8) [320,12,33,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6765 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6766 : Route 9 := (fun mask => (mask,id))

def c6766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6766 : Upper (D 8) (R 8) [320,12,33,144,96,128] 13 := by
  apply FastRouting.sound _ _ [320,12,33,144,96,128] 13 (by decide) (choices 1) [1,2,32] r6766 c6766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u851
  · exact u852
  · exact u853

def b6767 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 168 82 33 240 176 432), lower := (rows 321 14 37 168 82 33 64 128 256), losses := [] }

theorem u6767 : Upper (D 8) (R 8) [320,12,33,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6768 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 37 168 82 48 225 161 417), lower := (rows 321 14 37 168 82 48 64 128 256), losses := [] }

theorem u6768 : Upper (D 8) (R 8) [320,12,33,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6768 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6769 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 168 82 160 113 177 305), lower := (rows 321 14 37 168 82 160 64 128 256), losses := [] }

theorem u6769 : Upper (D 8) (R 8) [320,12,33,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6770 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 168 112 33 210 146 402), lower := (rows 321 14 37 168 112 33 64 128 256), losses := [] }

theorem u6770 : Upper (D 8) (R 8) [320,12,33,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6771 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 321 14 37 168 112 34 209 145 401), lower := (rows 321 14 37 168 112 34 64 128 256), losses := [] }

theorem u6771 : Upper (D 8) (R 8) [320,12,33,160,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6771 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6772 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 321 14 37 168 112 48 195 131 387), lower := (rows 321 14 37 168 112 48 64 128 256), losses := [] }

theorem u6772 : Upper (D 8) (R 8) [320,12,33,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6772 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6773 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 168 112 160 83 147 275), lower := (rows 321 14 37 168 112 160 64 128 256), losses := [] }

theorem u6773 : Upper (D 8) (R 8) [320,12,33,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6774 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 321 14 37 168 145 34 112 240 368), lower := (rows 321 14 37 168 145 34 64 128 256), losses := [] }

theorem u6774 : Upper (D 8) (R 8) [320,12,33,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6774 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6775 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 321 14 37 168 145 48 98 226 354), lower := (rows 321 14 37 168 145 48 64 128 256), losses := [] }

theorem u6775 : Upper (D 8) (R 8) [320,12,33,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6775 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6776 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 154, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 37 168 145 96 114 178 306), lower := (rows 321 14 37 168 145 96 64 128 256), losses := [] }

theorem u6776 : Upper (D 8) (R 8) [320,12,33,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6777 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 168 208 33 114 178 306), lower := (rows 321 14 37 168 208 33 64 128 256), losses := [] }

theorem u6777 : Upper (D 8) (R 8) [320,12,33,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6778 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 14 37 168 208 34 113 177 305), lower := (rows 321 14 37 168 208 34 64 128 256), losses := [] }

theorem u6778 : Upper (D 8) (R 8) [320,12,33,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6778 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6779 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 14 37 168 208 48 99 163 291), lower := (rows 321 14 37 168 208 48 64 128 256), losses := [] }

theorem u6779 : Upper (D 8) (R 8) [320,12,33,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6779 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6779
end Delivery.IrregularNine14.P08
