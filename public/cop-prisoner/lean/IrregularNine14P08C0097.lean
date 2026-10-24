import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0011

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5820 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 14 37 200 112 48 225 161 417), lower := (rows 259 14 37 200 112 48 64 128 256), losses := [] }

theorem u5820 : Upper (D 8) (R 8) [258,12,33,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5820 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5821 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 259 14 37 200 112 160 113 177 305), lower := (rows 259 14 37 200 112 160 64 128 256), losses := [] }

theorem u5821 : Upper (D 8) (R 8) [258,12,33,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5822 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 52 104 145 33 224 224 480), lower := (rows 259 14 52 104 145 33 64 128 256), losses := [] }

theorem u5822 : Upper (D 8) (R 8) [258,12,48,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5823 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 52 104 145 96 225 161 417), lower := (rows 259 14 52 104 145 96 64 128 256), losses := [] }

theorem u5823 : Upper (D 8) (R 8) [258,12,48,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5824 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 52 104 145 160 97 225 353), lower := (rows 259 14 52 104 145 160 64 128 256), losses := [] }

theorem u5824 : Upper (D 8) (R 8) [258,12,48,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5825 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 69 168 112 33 240 176 432), lower := (rows 259 14 69 168 112 33 64 128 256), losses := [] }

theorem u5825 : Upper (D 8) (R 8) [258,12,65,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5826 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 14 69 168 112 48 225 161 417), lower := (rows 259 14 69 168 112 48 64 128 256), losses := [] }

theorem u5826 : Upper (D 8) (R 8) [258,12,65,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5826 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5827 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 69 168 112 160 113 177 305), lower := (rows 259 14 69 168 112 160 64 128 256), losses := [] }

theorem u5827 : Upper (D 8) (R 8) [258,12,65,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5828 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 69 168 208 33 112 176 304), lower := (rows 259 14 69 168 208 33 64 128 256), losses := [] }

theorem u5828 : Upper (D 8) (R 8) [258,12,65,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5829 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 14 69 168 208 48 97 161 289), lower := (rows 259 14 69 168 208 48 64 128 256), losses := [] }

theorem u5829 : Upper (D 8) (R 8) [258,12,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5829 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5830 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 84 168 49 33 224 224 480), lower := (rows 259 14 84 168 49 33 64 128 256), losses := [] }

theorem u5830 : Upper (D 8) (R 8) [258,12,80,160,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5831 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 259 14 84 168 49 96 225 161 417), lower := (rows 259 14 84 168 49 96 64 128 256), losses := [] }

theorem u5831 : Upper (D 8) (R 8) [258,12,80,160,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5832 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 84 168 49 160 97 225 353), lower := (rows 259 14 84 168 49 160 64 128 256), losses := [] }

theorem u5832 : Upper (D 8) (R 8) [258,12,80,160,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5833 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 206, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 100 168 49 33 208 208 464), lower := (rows 259 14 100 168 49 33 64 128 256), losses := [] }

theorem u5833 : Upper (D 8) (R 8) [258,12,96,160,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5834 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 14 100 168 49 48 193 193 449), lower := (rows 259 14 100 168 49 48 64 128 256), losses := [] }

theorem u5834 : Upper (D 8) (R 8) [258,12,96,160,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5834 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5835 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 100 168 49 96 209 145 401), lower := (rows 259 14 100 168 49 96 64 128 256), losses := [] }

theorem u5835 : Upper (D 8) (R 8) [258,12,96,160,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5836 : Route 9 := (fun mask => (mask,id))

def c5836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5836 : Upper (D 8) (R 8) [258,12,96,160,192,1] 13 := by
  apply FastRouting.sound _ _ [258,12,96,160,192,1] 13 (by decide) (choices 1) [1,16,32] r5836 c5836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u715
  · exact u716
  · exact u717

def b5837 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 14 100 168 208 48 97 161 289), lower := (rows 259 14 100 168 208 48 64 128 256), losses := [] }

theorem u5837 : Upper (D 8) (R 8) [258,12,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5837 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5838 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 44 208 33 224 224 480), lower := (rows 259 35 28 44 208 33 64 128 256), losses := [] }

theorem u5838 : Upper (D 8) (R 8) [258,33,24,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5839 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 44, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 44 208 96 225 161 417), lower := (rows 259 35 28 44 208 96 64 128 256), losses := [] }

theorem u5839 : Upper (D 8) (R 8) [258,33,24,36,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5840 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 76 176 33 224 224 480), lower := (rows 259 35 28 76 176 33 64 128 256), losses := [] }

theorem u5840 : Upper (D 8) (R 8) [258,33,24,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5841 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 76 176 96 225 161 417), lower := (rows 259 35 28 76 176 96 64 128 256), losses := [] }

theorem u5841 : Upper (D 8) (R 8) [258,33,24,68,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5842 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 28 76 176 160 97 225 353), lower := (rows 259 35 28 76 176 160 64 128 256), losses := [] }

theorem u5842 : Upper (D 8) (R 8) [258,33,24,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5843 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 104 176 33 196 196 452), lower := (rows 259 35 28 104 176 33 64 128 256), losses := [] }

theorem u5843 : Upper (D 8) (R 8) [258,33,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5844 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 35 28 104 176 36 193 193 449), lower := (rows 259 35 28 104 176 36 64 128 256), losses := [] }

theorem u5844 : Upper (D 8) (R 8) [258,33,24,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5844 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5845 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 104 176 96 197 133 389), lower := (rows 259 35 28 104 176 96 64 128 256), losses := [] }

theorem u5845 : Upper (D 8) (R 8) [258,33,24,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5846 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 76 176 33 208 208 464), lower := (rows 259 35 44 76 176 33 64 128 256), losses := [] }

theorem u5846 : Upper (D 8) (R 8) [258,33,40,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5847 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 35 44 76 176 48 193 193 449), lower := (rows 259 35 44 76 176 48 64 128 256), losses := [] }

theorem u5847 : Upper (D 8) (R 8) [258,33,40,68,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5847 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5848 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 76 176 96 209 145 401), lower := (rows 259 35 44 76 176 96 64 128 256), losses := [] }

theorem u5848 : Upper (D 8) (R 8) [258,33,40,68,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5849 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 44 76 176 160 81 209 337), lower := (rows 259 35 44 76 176 160 64 128 256), losses := [] }

theorem u5849 : Upper (D 8) (R 8) [258,33,40,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5850 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 148 33 224 224 480), lower := (rows 259 35 44 88 148 33 64 128 256), losses := [] }

theorem u5850 : Upper (D 8) (R 8) [258,33,40,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5851 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 148 96 225 161 417), lower := (rows 259 35 44 88 148 96 64 128 256), losses := [] }

theorem u5851 : Upper (D 8) (R 8) [258,33,40,80,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5852 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 44 88 148 160 97 225 353), lower := (rows 259 35 44 88 148 160 64 128 256), losses := [] }

theorem u5852 : Upper (D 8) (R 8) [258,33,40,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5853 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 176 33 196 196 452), lower := (rows 259 35 44 88 176 33 64 128 256), losses := [] }

theorem u5853 : Upper (D 8) (R 8) [258,33,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5854 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 35 44 88 176 36 193 193 449), lower := (rows 259 35 44 88 176 36 64 128 256), losses := [] }

theorem u5854 : Upper (D 8) (R 8) [258,33,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5854 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5855 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 176 96 197 133 389), lower := (rows 259 35 44 88 176 96 64 128 256), losses := [] }

theorem u5855 : Upper (D 8) (R 8) [258,33,40,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5856 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 44 88 176 160 69 197 325), lower := (rows 259 35 44 88 176 160 64 128 256), losses := [] }

theorem u5856 : Upper (D 8) (R 8) [258,33,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5857 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 200 112 33 212 148 404), lower := (rows 259 35 44 200 112 33 64 128 256), losses := [] }

theorem u5857 : Upper (D 8) (R 8) [258,33,40,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5858 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 35 44 200 112 36 209 145 401), lower := (rows 259 35 44 200 112 36 64 128 256), losses := [] }

theorem u5858 : Upper (D 8) (R 8) [258,33,40,192,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5858 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5859 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 259 35 44 200 112 48 197 133 389), lower := (rows 259 35 44 200 112 48 64 128 256), losses := [] }

theorem u5859 : Upper (D 8) (R 8) [258,33,40,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5859 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5860 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 44 200 112 160 85 149 277), lower := (rows 259 35 44 200 112 160 64 128 256), losses := [] }

theorem u5860 : Upper (D 8) (R 8) [258,33,40,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5861 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 168 112 33 212 148 404), lower := (rows 259 35 76 168 112 33 64 128 256), losses := [] }

theorem u5861 : Upper (D 8) (R 8) [258,33,72,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5862 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 35 76 168 112 36 209 145 401), lower := (rows 259 35 76 168 112 36 64 128 256), losses := [] }

theorem u5862 : Upper (D 8) (R 8) [258,33,72,160,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5862 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5863 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 259 35 76 168 112 48 197 133 389), lower := (rows 259 35 76 168 112 48 64 128 256), losses := [] }

theorem u5863 : Upper (D 8) (R 8) [258,33,72,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5863 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5864 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 76 168 112 160 85 149 277), lower := (rows 259 35 76 168 112 160 64 128 256), losses := [] }

theorem u5864 : Upper (D 8) (R 8) [258,33,72,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5865 : PairBound 9 := { available := 52, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 168 208 33 116 180 308), lower := (rows 259 35 76 168 208 33 64 128 256), losses := [] }

theorem u5865 : Upper (D 8) (R 8) [258,33,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5866 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 35 76 168 208 36 113 177 305), lower := (rows 259 35 76 168 208 36 64 128 256), losses := [] }

theorem u5866 : Upper (D 8) (R 8) [258,33,72,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5866 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5867 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 259 35 76 168 208 48 101 165 293), lower := (rows 259 35 76 168 208 48 64 128 256), losses := [] }

theorem u5867 : Upper (D 8) (R 8) [258,33,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5867 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5868 : PairBound 9 := { available := 28, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 100 168 208 33 92 156 284), lower := (rows 259 35 100 168 208 33 64 128 256), losses := [] }

theorem u5868 : Upper (D 8) (R 8) [258,33,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5869 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 259 35 100 168 208 36 89 153 281), lower := (rows 259 35 100 168 208 36 64 128 256), losses := [] }

theorem u5869 : Upper (D 8) (R 8) [258,33,96,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5869 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5870 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 259 35 100 168 208 48 77 141 269), lower := (rows 259 35 100 168 208 48 64 128 256), losses := [] }

theorem u5870 : Upper (D 8) (R 8) [258,33,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5870 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5871 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 56 208 33 224 224 480), lower := (rows 259 38 13 56 208 33 64 128 256), losses := [] }

theorem u5871 : Upper (D 8) (R 8) [258,36,9,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5872 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 13 56 208 96 225 161 417), lower := (rows 259 38 13 56 208 96 64 128 256), losses := [] }

theorem u5872 : Upper (D 8) (R 8) [258,36,9,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5873 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 88 176 33 224 224 480), lower := (rows 259 38 13 88 176 33 64 128 256), losses := [] }

theorem u5873 : Upper (D 8) (R 8) [258,36,9,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5874 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 13 88 176 96 225 161 417), lower := (rows 259 38 13 88 176 96 64 128 256), losses := [] }

theorem u5874 : Upper (D 8) (R 8) [258,36,9,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5875 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 13 88 176 160 97 225 353), lower := (rows 259 38 13 88 176 160 64 128 256), losses := [] }

theorem u5875 : Upper (D 8) (R 8) [258,36,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5876 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 13 104 176 33 208 208 464), lower := (rows 259 38 13 104 176 33 64 128 256), losses := [] }

theorem u5876 : Upper (D 8) (R 8) [258,36,9,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5877 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 38 13 104 176 48 193 193 449), lower := (rows 259 38 13 104 176 48 64 128 256), losses := [] }

theorem u5877 : Upper (D 8) (R 8) [258,36,9,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5877 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5878 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 13 104 176 96 209 145 401), lower := (rows 259 38 13 104 176 96 64 128 256), losses := [] }

theorem u5878 : Upper (D 8) (R 8) [258,36,9,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5879 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 13 104 176 160 81 209 337), lower := (rows 259 38 13 104 176 160 64 128 256), losses := [] }

theorem u5879 : Upper (D 8) (R 8) [258,36,9,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5879
end Delivery.IrregularNine14.P08
