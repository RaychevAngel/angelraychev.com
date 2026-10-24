import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0005

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4740 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 70 265 81 36 68 176 304), lower := (rows 11 162 70 265 81 36 68 128 256), losses := [] }

theorem u4740 : Upper (D 6) (R 6) [10,160,66,257,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4741 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 70 265 81 36 80 164 292), lower := (rows 11 162 70 265 81 36 80 128 256), losses := [] }

theorem u4741 : Upper (D 6) (R 6) [10,160,66,257,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4741 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4742 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 265 81 36 96 148 276), lower := (rows 11 162 70 265 81 36 96 128 256), losses := [] }

theorem u4742 : Upper (D 6) (R 6) [10,160,66,257,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4743 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 182, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 70 265 112 36 65 148 276), lower := (rows 11 162 70 265 112 36 65 128 256), losses := [] }

theorem u4743 : Upper (D 6) (R 6) [10,160,66,257,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4744 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 70 265 112 36 68 145 273), lower := (rows 11 162 70 265 112 36 68 128 256), losses := [] }

theorem u4744 : Upper (D 6) (R 6) [10,160,66,257,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4745 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 70 265 112 36 80 133 261), lower := (rows 11 162 70 265 112 36 80 128 256), losses := [] }

theorem u4745 : Upper (D 6) (R 6) [10,160,66,257,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4745 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4746 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 268 21 33 80 224 352), lower := (rows 11 162 70 268 21 33 80 128 256), losses := [] }

theorem u4746 : Upper (D 6) (R 6) [10,160,66,260,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4746 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4747 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 268 21 33 96 208 336), lower := (rows 11 162 70 268 21 33 96 128 256), losses := [] }

theorem u4747 : Upper (D 6) (R 6) [10,160,66,260,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4748 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 70 268 21 96 65 176 304), lower := (rows 11 162 70 268 21 96 65 128 256), losses := [] }

theorem u4748 : Upper (D 6) (R 6) [10,160,66,260,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4749 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 268 21 96 80 161 289), lower := (rows 11 162 70 268 21 96 80 128 256), losses := [] }

theorem u4749 : Upper (D 6) (R 6) [10,160,66,260,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4749 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4750 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 70 268 21 96 96 145 273), lower := (rows 11 162 70 268 21 96 96 128 256), losses := [] }

theorem u4750 : Upper (D 6) (R 6) [10,160,66,260,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4751 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 162 70 268 49 96 65 148 276), lower := (rows 11 162 70 268 49 96 65 128 256), losses := [] }

theorem u4751 : Upper (D 6) (R 6) [10,160,66,260,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4752 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 130, targets := 68 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 70 268 49 96 68 145 273), lower := (rows 11 162 70 268 49 96 68 128 256), losses := [] }

theorem u4752 : Upper (D 6) (R 6) [10,160,66,260,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4753 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 265, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 11 162 70 268 49 96 80 133 261), lower := (rows 11 162 70 268 49 96 80 128 256), losses := [] }

theorem u4753 : Upper (D 6) (R 6) [10,160,66,260,33,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4753 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4754 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 162 70 268 52 33 65 208 336), lower := (rows 11 162 70 268 52 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 20 97 97 148 276), good := (rows 105 224 508 412 508 97 97 128 256) }] }

theorem u4754 : Upper (D 6) (R 6) [10,160,66,260,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4755 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 162 70 268 52 33 80 193 321), lower := (rows 11 162 70 268 52 33 80 128 256), losses := [] }

theorem u4755 : Upper (D 6) (R 6) [10,160,66,260,36,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4755 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4756 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 4, region := 162, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 162 70 268 81 33 68 176 304), lower := (rows 11 162 70 268 81 33 68 128 256), losses := [] }

theorem u4756 : Upper (D 6) (R 6) [10,160,66,260,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4757 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 70 268 81 33 80 164 292), lower := (rows 11 162 70 268 81 33 80 128 256), losses := [] }

theorem u4757 : Upper (D 6) (R 6) [10,160,66,260,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4757 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4758 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 268 81 33 96 148 276), lower := (rows 11 162 70 268 81 33 96 128 256), losses := [] }

theorem u4758 : Upper (D 6) (R 6) [10,160,66,260,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4759 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 70 268 81 36 65 176 304), lower := (rows 11 162 70 268 81 36 65 128 256), losses := [] }

theorem u4759 : Upper (D 6) (R 6) [10,160,66,260,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4760 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 70 268 81 36 80 161 289), lower := (rows 11 162 70 268 81 36 80 128 256), losses := [] }

theorem u4760 : Upper (D 6) (R 6) [10,160,66,260,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4760 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4761 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 268 81 36 96 145 273), lower := (rows 11 162 70 268 81 36 96 128 256), losses := [] }

theorem u4761 : Upper (D 6) (R 6) [10,160,66,260,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4762 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 70 268 81 48 65 164 292), lower := (rows 11 162 70 268 81 48 65 128 256), losses := [] }

theorem u4762 : Upper (D 6) (R 6) [10,160,66,260,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4762 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4763 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 268 81 48 68 161 289), lower := (rows 11 162 70 268 81 48 68 128 256), losses := [] }

theorem u4763 : Upper (D 6) (R 6) [10,160,66,260,65,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4763 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4764 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 265, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 70 268 81 48 96 133 261), lower := (rows 11 162 70 268 81 48 96 128 256), losses := [] }

theorem u4764 : Upper (D 6) (R 6) [10,160,66,260,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4764 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4765 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 70 268 112 33 65 148 276), lower := (rows 11 162 70 268 112 33 65 128 256), losses := [] }

theorem u4765 : Upper (D 6) (R 6) [10,160,66,260,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4766 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 84, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 11 162 70 268 112 33 68 145 273), lower := (rows 11 162 70 268 112 33 68 128 256), losses := [] }

theorem u4766 : Upper (D 6) (R 6) [10,160,66,260,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4767 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 70 268 112 33 80 133 261), lower := (rows 11 162 70 268 112 33 80 128 256), losses := [] }

theorem u4767 : Upper (D 6) (R 6) [10,160,66,260,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4767 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4768 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 162 70 268 112 36 65 145 273), lower := (rows 11 162 70 268 112 36 65 128 256), losses := [] }

theorem u4768 : Upper (D 6) (R 6) [10,160,66,260,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4769 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 70 268 112 36 80 129 257), lower := (rows 11 162 70 268 112 36 80 128 256), losses := [] }

theorem u4769 : Upper (D 6) (R 6) [10,160,66,260,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4769 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4770 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 6, region := 166, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 70 280 21 36 65 224 352), lower := (rows 11 162 70 280 21 36 65 128 256), losses := [] }

theorem u4770 : Upper (D 6) (R 6) [10,160,66,272,5,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4771 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 280 21 36 96 193 321), lower := (rows 11 162 70 280 21 36 96 128 256), losses := [] }

theorem u4771 : Upper (D 6) (R 6) [10,160,66,272,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4772 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 5, region := 134, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 70 280 21 96 65 164 292), lower := (rows 11 162 70 280 21 96 65 128 256), losses := [] }

theorem u4772 : Upper (D 6) (R 6) [10,160,66,272,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4773 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 70 280 21 96 68 161 289), lower := (rows 11 162 70 280 21 96 68 128 256), losses := [] }

theorem u4773 : Upper (D 6) (R 6) [10,160,66,272,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4774 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 70 280 21 96 96 133 261), lower := (rows 11 162 70 280 21 96 96 128 256), losses := [] }

theorem u4774 : Upper (D 6) (R 6) [10,160,66,272,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4775 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 166, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 280 49 36 65 196 324), lower := (rows 11 162 70 280 49 36 65 128 256), losses := [] }

theorem u4775 : Upper (D 6) (R 6) [10,160,66,272,33,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4776 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 280 49 36 68 193 321), lower := (rows 11 162 70 280 49 36 68 128 256), losses := [] }

theorem u4776 : Upper (D 6) (R 6) [10,160,66,272,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4777 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 5, region := 134, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 162 70 280 49 96 65 132 260), lower := (rows 11 162 70 280 49 96 65 128 256), losses := [] }

theorem u4777 : Upper (D 6) (R 6) [10,160,66,272,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4778 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 280 49 96 68 133 261), lower := (rows 11 162 70 280 49 96 68 128 256), losses := [] }

theorem u4778 : Upper (D 6) (R 6) [10,160,66,272,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4779 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,5),(3,0)], upper := (rows 11 162 70 280 52 33 65 196 324), lower := (rows 11 162 70 280 52 33 65 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 32 64 132 260), good := (rows 10 162 454 282 446 32 64 128 256) }] }

theorem u4779 : Upper (D 6) (R 6) [10,160,66,272,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4780 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 11 162 70 280 52 33 68 193 321), lower := (rows 11 162 70 280 52 33 68 128 256), losses := [] }

theorem u4780 : Upper (D 6) (R 6) [10,160,66,272,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4781 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 70 280 81 33 68 164 292), lower := (rows 11 162 70 280 81 33 68 128 256), losses := [] }

theorem u4781 : Upper (D 6) (R 6) [10,160,66,272,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4782 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 280 81 33 96 132 260), lower := (rows 11 162 70 280 81 33 96 128 256), losses := [] }

theorem u4782 : Upper (D 6) (R 6) [10,160,66,272,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4783 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 70 280 81 36 65 164 292), lower := (rows 11 162 70 280 81 36 65 128 256), losses := [] }

theorem u4783 : Upper (D 6) (R 6) [10,160,66,272,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4784 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 70 280 81 36 68 161 289), lower := (rows 11 162 70 280 81 36 68 128 256), losses := [] }

theorem u4784 : Upper (D 6) (R 6) [10,160,66,272,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4785 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 280 81 36 96 133 261), lower := (rows 11 162 70 280 81 36 96 128 256), losses := [] }

theorem u4785 : Upper (D 6) (R 6) [10,160,66,272,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4786 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 70 280 112 33 65 132 260), lower := (rows 11 162 70 280 112 33 65 128 256), losses := [] }

theorem u4786 : Upper (D 6) (R 6) [10,160,66,272,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4787 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 11 162 70 280 112 33 68 133 261), lower := (rows 11 162 70 280 112 33 68 128 256), losses := [] }

theorem u4787 : Upper (D 6) (R 6) [10,160,66,272,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4788 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 162 70 296 81 33 68 148 276), lower := (rows 11 162 70 296 81 33 68 128 256), losses := [] }

theorem u4788 : Upper (D 6) (R 6) [10,160,66,288,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4789 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 70 296 81 33 80 132 260), lower := (rows 11 162 70 296 81 33 80 128 256), losses := [] }

theorem u4789 : Upper (D 6) (R 6) [10,160,66,288,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4789 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4790 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 70 296 81 36 65 148 276), lower := (rows 11 162 70 296 81 36 65 128 256), losses := [] }

theorem u4790 : Upper (D 6) (R 6) [10,160,66,288,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4791 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 70 296 81 36 68 145 273), lower := (rows 11 162 70 296 81 36 68 128 256), losses := [] }

theorem u4791 : Upper (D 6) (R 6) [10,160,66,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4792 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 70 296 81 36 80 133 261), lower := (rows 11 162 70 296 81 36 80 128 256), losses := [] }

theorem u4792 : Upper (D 6) (R 6) [10,160,66,288,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4792 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4793 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 4, region := 162, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 162 70 328 21 33 68 176 304), lower := (rows 11 162 70 328 21 33 68 128 256), losses := [] }

theorem u4793 : Upper (D 6) (R 6) [10,160,66,320,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4794 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 328 21 33 80 164 292), lower := (rows 11 162 70 328 21 33 80 128 256), losses := [] }

theorem u4794 : Upper (D 6) (R 6) [10,160,66,320,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4794 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4795 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 328 21 33 96 148 276), lower := (rows 11 162 70 328 21 33 96 128 256), losses := [] }

theorem u4795 : Upper (D 6) (R 6) [10,160,66,320,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4796 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 70 328 21 36 65 176 304), lower := (rows 11 162 70 328 21 36 65 128 256), losses := [] }

theorem u4796 : Upper (D 6) (R 6) [10,160,66,320,5,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4797 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 328 21 36 80 161 289), lower := (rows 11 162 70 328 21 36 80 128 256), losses := [] }

theorem u4797 : Upper (D 6) (R 6) [10,160,66,320,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4797 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4798 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 328 21 36 96 145 273), lower := (rows 11 162 70 328 21 36 96 128 256), losses := [] }

theorem u4798 : Upper (D 6) (R 6) [10,160,66,320,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4799 : Route 9 := (fun mask => (mask,id))

def c4799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4799 : Upper (D 6) (R 6) [10,160,66,320,33,4,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,320,33,4,1] 13 (by decide) (choices 1) [4,16] r4799 c4799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u358
  · exact u359

#print axioms u4799
end Delivery.IrregularNine14.P06
