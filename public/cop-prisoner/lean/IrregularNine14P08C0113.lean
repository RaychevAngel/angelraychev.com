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

def b6780 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 200 50 33 240 176 432), lower := (rows 321 14 37 200 50 33 64 128 256), losses := [] }

theorem u6780 : Upper (D 8) (R 8) [320,12,33,192,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6781 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 37 200 50 48 225 161 417), lower := (rows 321 14 37 200 50 48 64 128 256), losses := [] }

theorem u6781 : Upper (D 8) (R 8) [320,12,33,192,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6781 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6782 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 37 200 50 160 113 177 305), lower := (rows 321 14 37 200 50 160 64 128 256), losses := [] }

theorem u6782 : Upper (D 8) (R 8) [320,12,33,192,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6783 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 321 14 37 200 145 34 112 176 304), lower := (rows 321 14 37 200 145 34 64 128 256), losses := [] }

theorem u6783 : Upper (D 8) (R 8) [320,12,33,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6783 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6784 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 321 14 37 200 145 48 98 162 290), lower := (rows 321 14 37 200 145 48 64 128 256), losses := [] }

theorem u6784 : Upper (D 8) (R 8) [320,12,33,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6784 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6785 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 200 176 33 114 178 306), lower := (rows 321 14 37 200 176 33 64 128 256), losses := [] }

theorem u6785 : Upper (D 8) (R 8) [320,12,33,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6786 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 14 37 200 176 34 113 177 305), lower := (rows 321 14 37 200 176 34 64 128 256), losses := [] }

theorem u6786 : Upper (D 8) (R 8) [320,12,33,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6786 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6787 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 14 37 200 176 48 99 163 291), lower := (rows 321 14 37 200 176 48 64 128 256), losses := [] }

theorem u6787 : Upper (D 8) (R 8) [320,12,33,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6787 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6788 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 321 14 38 137 49 48 224 224 480), lower := (rows 321 14 38 137 49 48 64 128 256), losses := [] }

theorem u6788 : Upper (D 8) (R 8) [320,12,34,129,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6788 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6789 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 142, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 38 137 49 96 240 176 432), lower := (rows 321 14 38 137 49 96 64 128 256), losses := [] }

theorem u6789 : Upper (D 8) (R 8) [320,12,34,129,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6790 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 38 137 49 160 112 240 368), lower := (rows 321 14 38 137 49 160 64 128 256), losses := [] }

theorem u6790 : Upper (D 8) (R 8) [320,12,34,129,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6791 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 38 137 112 33 240 176 432), lower := (rows 321 14 38 137 112 33 64 128 256), losses := [] }

theorem u6791 : Upper (D 8) (R 8) [320,12,34,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6792 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 38 137 112 48 225 161 417), lower := (rows 321 14 38 137 112 48 64 128 256), losses := [] }

theorem u6792 : Upper (D 8) (R 8) [320,12,34,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6792 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6793 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 137 112 160 113 177 305), lower := (rows 321 14 38 137 112 160 64 128 256), losses := [] }

theorem u6793 : Upper (D 8) (R 8) [320,12,34,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6794 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 152 49 33 224 224 480), lower := (rows 321 14 38 152 49 33 64 128 256), losses := [] }

theorem u6794 : Upper (D 8) (R 8) [320,12,34,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6795 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 142, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 38 152 49 96 225 161 417), lower := (rows 321 14 38 152 49 96 64 128 256), losses := [] }

theorem u6795 : Upper (D 8) (R 8) [320,12,34,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6796 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 152 49 160 97 225 353), lower := (rows 321 14 38 152 49 160 64 128 256), losses := [] }

theorem u6796 : Upper (D 8) (R 8) [320,12,34,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6797 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 321 14 38 152 112 33 225 161 417), lower := (rows 321 14 38 152 112 33 64 128 256), losses := [] }

theorem u6797 : Upper (D 8) (R 8) [320,12,34,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6798 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 152 112 160 97 161 289), lower := (rows 321 14 38 152 112 160 64 128 256), losses := [] }

theorem u6798 : Upper (D 8) (R 8) [320,12,34,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6799 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 52 104 145 33 226 162 418), lower := (rows 321 14 52 104 145 33 64 128 256), losses := [] }

theorem u6799 : Upper (D 8) (R 8) [320,12,48,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6800 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 52 104 145 34 225 161 417), lower := (rows 321 14 52 104 145 34 64 128 256), losses := [] }

theorem u6800 : Upper (D 8) (R 8) [320,12,48,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6800 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6801 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 52 104 145 160 99 163 291), lower := (rows 321 14 52 104 145 160 64 128 256), losses := [] }

theorem u6801 : Upper (D 8) (R 8) [320,12,48,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6802 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 321 14 52 104 146 33 225 161 417), lower := (rows 321 14 52 104 146 33 64 128 256), losses := [] }

theorem u6802 : Upper (D 8) (R 8) [320,12,48,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6803 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 52 104 146 160 97 161 289), lower := (rows 321 14 52 104 146 160 64 128 256), losses := [] }

theorem u6803 : Upper (D 8) (R 8) [320,12,48,96,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6804 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 321 14 84 137 49 34 224 160 416), lower := (rows 321 14 84 137 49 34 64 128 256), losses := [] }

theorem u6804 : Upper (D 8) (R 8) [320,12,80,129,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6804 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6805 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 84 137 49 160 98 162 290), lower := (rows 321 14 84 137 49 160 64 128 256), losses := [] }

theorem u6805 : Upper (D 8) (R 8) [320,12,80,129,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6806 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 84 168 49 33 226 162 418), lower := (rows 321 14 84 168 49 33 64 128 256), losses := [] }

theorem u6806 : Upper (D 8) (R 8) [320,12,80,160,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6807 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 84 168 49 34 225 161 417), lower := (rows 321 14 84 168 49 34 64 128 256), losses := [] }

theorem u6807 : Upper (D 8) (R 8) [320,12,80,160,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6807 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6808 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 84 168 49 160 99 163 291), lower := (rows 321 14 84 168 49 160 64 128 256), losses := [] }

theorem u6808 : Upper (D 8) (R 8) [320,12,80,160,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6809 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 321 14 100 137 49 34 240 176 432), lower := (rows 321 14 100 137 49 34 64 128 256), losses := [] }

theorem u6809 : Upper (D 8) (R 8) [320,12,96,129,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6809 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6810 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 321 14 100 137 49 48 226 162 418), lower := (rows 321 14 100 137 49 48 64 128 256), losses := [] }

theorem u6810 : Upper (D 8) (R 8) [320,12,96,129,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6810 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6811 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 100 137 49 160 114 178 306), lower := (rows 321 14 100 137 49 160 64 128 256), losses := [] }

theorem u6811 : Upper (D 8) (R 8) [320,12,96,129,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6812 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 321 14 100 137 50 33 240 176 432), lower := (rows 321 14 100 137 50 33 64 128 256), losses := [] }

theorem u6812 : Upper (D 8) (R 8) [320,12,96,129,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6813 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 100 137 50 48 225 161 417), lower := (rows 321 14 100 137 50 48 64 128 256), losses := [] }

theorem u6813 : Upper (D 8) (R 8) [320,12,96,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6813 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6814 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 100 137 50 160 113 177 305), lower := (rows 321 14 100 137 50 160 64 128 256), losses := [] }

theorem u6814 : Upper (D 8) (R 8) [320,12,96,129,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6815 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 321 14 100 137 176 33 114 178 306), lower := (rows 321 14 100 137 176 33 64 128 256), losses := [] }

theorem u6815 : Upper (D 8) (R 8) [320,12,96,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6816 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 14 100 137 176 34 113 177 305), lower := (rows 321 14 100 137 176 34 64 128 256), losses := [] }

theorem u6816 : Upper (D 8) (R 8) [320,12,96,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6816 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6817 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 14 100 137 176 48 99 163 291), lower := (rows 321 14 100 137 176 48 64 128 256), losses := [] }

theorem u6817 : Upper (D 8) (R 8) [320,12,96,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6817 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6818 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 100 152 49 33 226 162 418), lower := (rows 321 14 100 152 49 33 64 128 256), losses := [] }

theorem u6818 : Upper (D 8) (R 8) [320,12,96,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6819 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 14 100 152 49 34 225 161 417), lower := (rows 321 14 100 152 49 34 64 128 256), losses := [] }

theorem u6819 : Upper (D 8) (R 8) [320,12,96,144,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6819 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6820 : Route 9 := (fun mask => (mask,id))

def c6820 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6820 : Upper (D 8) (R 8) [320,12,96,144,33,128] 13 := by
  apply FastRouting.sound _ _ [320,12,96,144,33,128] 13 (by decide) (choices 1) [1,2,32] r6820 c6820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u854
  · exact u855
  · exact u856

def b6821 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 321 14 100 152 50 33 225 161 417), lower := (rows 321 14 100 152 50 33 64 128 256), losses := [] }

theorem u6821 : Upper (D 8) (R 8) [320,12,96,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6822 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 100 152 50 160 97 161 289), lower := (rows 321 14 100 152 50 160 64 128 256), losses := [] }

theorem u6822 : Upper (D 8) (R 8) [320,12,96,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6823 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 100 168 49 33 210 146 402), lower := (rows 321 14 100 168 49 33 64 128 256), losses := [] }

theorem u6823 : Upper (D 8) (R 8) [320,12,96,160,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6824 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 321 14 100 168 49 34 209 145 401), lower := (rows 321 14 100 168 49 34 64 128 256), losses := [] }

theorem u6824 : Upper (D 8) (R 8) [320,12,96,160,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6824 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6825 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 321 14 100 168 49 48 195 131 387), lower := (rows 321 14 100 168 49 48 64 128 256), losses := [] }

theorem u6825 : Upper (D 8) (R 8) [320,12,96,160,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6825 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6826 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 100 168 49 160 83 147 275), lower := (rows 321 14 100 168 49 160 64 128 256), losses := [] }

theorem u6826 : Upper (D 8) (R 8) [320,12,96,160,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6827 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 321 14 100 168 145 33 114 178 306), lower := (rows 321 14 100 168 145 33 64 128 256), losses := [] }

theorem u6827 : Upper (D 8) (R 8) [320,12,96,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6828 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 14 100 168 145 34 113 177 305), lower := (rows 321 14 100 168 145 34 64 128 256), losses := [] }

theorem u6828 : Upper (D 8) (R 8) [320,12,96,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6828 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6829 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 14 100 168 145 48 99 163 291), lower := (rows 321 14 100 168 145 48 64 128 256), losses := [] }

theorem u6829 : Upper (D 8) (R 8) [320,12,96,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6829 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6830 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 321 35 44 74 145 36 240 176 432), lower := (rows 321 35 44 74 145 36 64 128 256), losses := [] }

theorem u6830 : Upper (D 8) (R 8) [320,33,40,66,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6830 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6831 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 321 35 44 74 145 48 228 164 420), lower := (rows 321 35 44 74 145 48 64 128 256), losses := [] }

theorem u6831 : Upper (D 8) (R 8) [320,33,40,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6831 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6832 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 74 145 160 116 180 308), lower := (rows 321 35 44 74 145 160 64 128 256), losses := [] }

theorem u6832 : Upper (D 8) (R 8) [320,33,40,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6833 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 321 35 44 74 148 33 240 176 432), lower := (rows 321 35 44 74 148 33 64 128 256), losses := [] }

theorem u6833 : Upper (D 8) (R 8) [320,33,40,66,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6834 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 35 44 74 148 48 225 161 417), lower := (rows 321 35 44 74 148 48 64 128 256), losses := [] }

theorem u6834 : Upper (D 8) (R 8) [320,33,40,66,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6834 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6835 : Route 9 := (fun mask => (mask,id))

def c6835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6835 : Upper (D 8) (R 8) [320,33,40,66,132,128] 13 := by
  apply FastRouting.sound _ _ [320,33,40,66,132,128] 13 (by decide) (choices 1) [1,16,32] r6835 c6835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u857
  · exact u858
  · exact u859

def b6836 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 321 35 44 74 176 33 212 148 404), lower := (rows 321 35 44 74 176 33 64 128 256), losses := [] }

theorem u6836 : Upper (D 8) (R 8) [320,33,40,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6837 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 321 35 44 74 176 36 209 145 401), lower := (rows 321 35 44 74 176 36 64 128 256), losses := [] }

theorem u6837 : Upper (D 8) (R 8) [320,33,40,66,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6837 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6838 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 321 35 44 74 176 48 197 133 389), lower := (rows 321 35 44 74 176 48 64 128 256), losses := [] }

theorem u6838 : Upper (D 8) (R 8) [320,33,40,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6838 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6839 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 74 176 160 85 149 277), lower := (rows 321 35 44 74 176 160 64 128 256), losses := [] }

theorem u6839 : Upper (D 8) (R 8) [320,33,40,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6839
end Delivery.IrregularNine14.P08
