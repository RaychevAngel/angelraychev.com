import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4620 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 265, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 69 265 22 96 96 148 276), lower := (rows 11 162 69 265 22 96 96 128 256), losses := [] }

theorem u4620 : Upper (D 6) (R 6) [10,160,65,257,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4621 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 2, region := 178, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 69 265 82 36 68 176 304), lower := (rows 11 162 69 265 82 36 68 128 256), losses := [] }

theorem u4621 : Upper (D 6) (R 6) [10,160,65,257,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4622 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 162 69 265 82 36 80 164 292), lower := (rows 11 162 69 265 82 36 80 128 256), losses := [] }

theorem u4622 : Upper (D 6) (R 6) [10,160,65,257,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4622 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4623 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 69 265 82 36 96 148 276), lower := (rows 11 162 69 265 82 36 96 128 256), losses := [] }

theorem u4623 : Upper (D 6) (R 6) [10,160,65,257,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4624 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 268 22 33 80 224 352), lower := (rows 11 162 69 268 22 33 80 128 256), losses := [] }

theorem u4624 : Upper (D 6) (R 6) [10,160,65,260,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4624 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4625 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 162 69 268 22 33 96 208 336), lower := (rows 11 162 69 268 22 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 98 144 272), good := (rows 74 226 68 268 478 96 96 128 256) },{ target := 1, region := (rows 1 0 37 24 16 37 127 144 272), good := (rows 109 228 101 364 508 101 100 128 256) }] }

theorem u4625 : Upper (D 6) (R 6) [10,160,65,260,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4626 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 162 69 268 22 48 65 224 352), lower := (rows 11 162 69 268 22 48 65 128 256), losses := [] }

theorem u4626 : Upper (D 6) (R 6) [10,160,65,260,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4626 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4627 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 264, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 11 162 69 268 22 48 96 193 321), lower := (rows 11 162 69 268 22 48 96 128 256), losses := [] }

theorem u4627 : Upper (D 6) (R 6) [10,160,65,260,6,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4627 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4628 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 268 22 96 65 176 304), lower := (rows 11 162 69 268 22 96 65 128 256), losses := [] }

theorem u4628 : Upper (D 6) (R 6) [10,160,65,260,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4629 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 268 22 96 80 161 289), lower := (rows 11 162 69 268 22 96 80 128 256), losses := [] }

theorem u4629 : Upper (D 6) (R 6) [10,160,65,260,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4629 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4630 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 265, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 69 268 22 96 96 145 273), lower := (rows 11 162 69 268 22 96 96 128 256), losses := [] }

theorem u4630 : Upper (D 6) (R 6) [10,160,65,260,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4631 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 312, targets := 2 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 11 162 69 268 49 96 66 148 276), lower := (rows 11 162 69 268 49 96 66 128 256), losses := [] }

theorem u4631 : Upper (D 6) (R 6) [10,160,65,260,33,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4632 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 268 49 96 68 146 274), lower := (rows 11 162 69 268 49 96 68 128 256), losses := [] }

theorem u4632 : Upper (D 6) (R 6) [10,160,65,260,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4633 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 162 69 268 49 96 80 134 262), lower := (rows 11 162 69 268 49 96 80 128 256), losses := [] }

theorem u4633 : Upper (D 6) (R 6) [10,160,65,260,33,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4633 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4634 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 2, region := 178, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 162 69 268 82 33 68 176 304), lower := (rows 11 162 69 268 82 33 68 128 256), losses := [] }

theorem u4634 : Upper (D 6) (R 6) [10,160,65,260,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4635 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 162 69 268 82 33 80 164 292), lower := (rows 11 162 69 268 82 33 80 128 256), losses := [] }

theorem u4635 : Upper (D 6) (R 6) [10,160,65,260,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4635 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4636 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 69 268 82 33 96 148 276), lower := (rows 11 162 69 268 82 33 96 128 256), losses := [] }

theorem u4636 : Upper (D 6) (R 6) [10,160,65,260,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4637 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 268 82 36 65 176 304), lower := (rows 11 162 69 268 82 36 65 128 256), losses := [] }

theorem u4637 : Upper (D 6) (R 6) [10,160,65,260,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4638 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 162 69 268 82 36 80 161 289), lower := (rows 11 162 69 268 82 36 80 128 256), losses := [] }

theorem u4638 : Upper (D 6) (R 6) [10,160,65,260,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4638 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4639 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 69 268 82 36 96 145 273), lower := (rows 11 162 69 268 82 36 96 128 256), losses := [] }

theorem u4639 : Upper (D 6) (R 6) [10,160,65,260,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4640 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 162 69 268 82 48 65 164 292), lower := (rows 11 162 69 268 82 48 65 128 256), losses := [] }

theorem u4640 : Upper (D 6) (R 6) [10,160,65,260,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4640 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4641 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 268 82 48 68 161 289), lower := (rows 11 162 69 268 82 48 68 128 256), losses := [] }

theorem u4641 : Upper (D 6) (R 6) [10,160,65,260,66,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4641 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4642 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 114, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 11 162 69 268 82 48 96 133 261), lower := (rows 11 162 69 268 82 48 96 128 256), losses := [] }

theorem u4642 : Upper (D 6) (R 6) [10,160,65,260,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4642 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4643 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 2, region := 312, targets := 2 }], pairs := [(3,1),(4,0),(4,2)], upper := (rows 11 162 69 268 112 33 66 148 276), lower := (rows 11 162 69 268 112 33 66 128 256), losses := [] }

theorem u4643 : Upper (D 6) (R 6) [10,160,65,260,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4644 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 268 112 33 68 146 274), lower := (rows 11 162 69 268 112 33 68 128 256), losses := [] }

theorem u4644 : Upper (D 6) (R 6) [10,160,65,260,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4645 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 69 268 112 33 80 134 262), lower := (rows 11 162 69 268 112 33 80 128 256), losses := [] }

theorem u4645 : Upper (D 6) (R 6) [10,160,65,260,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4645 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4646 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 268 112 36 65 146 274), lower := (rows 11 162 69 268 112 36 65 128 256), losses := [] }

theorem u4646 : Upper (D 6) (R 6) [10,160,65,260,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4647 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 2, region := 312, targets := 2 }], pairs := [(3,1),(4,0),(4,2)], upper := (rows 11 162 69 268 112 36 66 145 273), lower := (rows 11 162 69 268 112 36 66 128 256), losses := [] }

theorem u4647 : Upper (D 6) (R 6) [10,160,65,260,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4648 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 69 268 112 36 80 131 259), lower := (rows 11 162 69 268 112 36 80 128 256), losses := [] }

theorem u4648 : Upper (D 6) (R 6) [10,160,65,260,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4648 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4649 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 69 280 22 33 68 224 352), lower := (rows 11 162 69 280 22 33 68 128 256), losses := [] }

theorem u4649 : Upper (D 6) (R 6) [10,160,65,272,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4650 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 162 69 280 22 33 96 196 324), lower := (rows 11 162 69 280 22 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 98 148 276), good := (rows 74 226 452 408 478 96 96 128 256) },{ target := 1, region := (rows 1 0 37 24 16 37 119 247 375), good := (rows 493 484 485 472 508 485 484 128 256) }] }

theorem u4650 : Upper (D 6) (R 6) [10,160,65,272,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4651 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 280 22 36 65 224 352), lower := (rows 11 162 69 280 22 36 65 128 256), losses := [] }

theorem u4651 : Upper (D 6) (R 6) [10,160,65,272,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4652 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 11 162 69 280 22 36 96 193 321), lower := (rows 11 162 69 280 22 36 96 128 256), losses := [{ target := 1, region := (rows 1 0 5 24 16 53 127 133 261), good := (rows 493 224 485 376 508 484 96 128 256) },{ target := 2, region := (rows 17 34 0 24 16 32 98 149 277), good := (rows 459 226 449 409 475 482 98 128 256) }] }

theorem u4652 : Upper (D 6) (R 6) [10,160,65,272,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4653 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 280 22 96 65 164 292), lower := (rows 11 162 69 280 22 96 65 128 256), losses := [] }

theorem u4653 : Upper (D 6) (R 6) [10,160,65,272,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4654 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 69 280 22 96 68 161 289), lower := (rows 11 162 69 280 22 96 68 128 256), losses := [] }

theorem u4654 : Upper (D 6) (R 6) [10,160,65,272,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4655 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 265, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 69 280 22 96 96 133 261), lower := (rows 11 162 69 280 22 96 96 128 256), losses := [] }

theorem u4655 : Upper (D 6) (R 6) [10,160,65,272,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4656 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 280 82 36 65 164 292), lower := (rows 11 162 69 280 82 36 65 128 256), losses := [] }

theorem u4656 : Upper (D 6) (R 6) [10,160,65,272,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4657 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 69 280 82 36 68 161 289), lower := (rows 11 162 69 280 82 36 68 128 256), losses := [] }

theorem u4657 : Upper (D 6) (R 6) [10,160,65,272,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4658 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 269, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 69 280 82 36 96 133 261), lower := (rows 11 162 69 280 82 36 96 128 256), losses := [] }

theorem u4658 : Upper (D 6) (R 6) [10,160,65,272,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4659 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 296 22 36 65 208 336), lower := (rows 11 162 69 296 22 36 65 128 256), losses := [] }

theorem u4659 : Upper (D 6) (R 6) [10,160,65,288,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4660 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 296 22 36 80 193 321), lower := (rows 11 162 69 296 22 36 80 128 256), losses := [] }

theorem u4660 : Upper (D 6) (R 6) [10,160,65,288,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4660 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4661 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 296 22 96 65 148 276), lower := (rows 11 162 69 296 22 96 65 128 256), losses := [] }

theorem u4661 : Upper (D 6) (R 6) [10,160,65,288,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4662 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 69 296 22 96 68 145 273), lower := (rows 11 162 69 296 22 96 68 128 256), losses := [] }

theorem u4662 : Upper (D 6) (R 6) [10,160,65,288,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4663 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 296 22 96 80 133 261), lower := (rows 11 162 69 296 22 96 80 128 256), losses := [] }

theorem u4663 : Upper (D 6) (R 6) [10,160,65,288,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4663 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4664 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 69 296 82 33 68 148 276), lower := (rows 11 162 69 296 82 33 68 128 256), losses := [] }

theorem u4664 : Upper (D 6) (R 6) [10,160,65,288,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4665 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 162 69 296 82 33 80 132 260), lower := (rows 11 162 69 296 82 33 80 128 256), losses := [] }

theorem u4665 : Upper (D 6) (R 6) [10,160,65,288,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4665 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4666 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 296 82 36 65 148 276), lower := (rows 11 162 69 296 82 36 65 128 256), losses := [] }

theorem u4666 : Upper (D 6) (R 6) [10,160,65,288,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4667 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 69 296 82 36 68 145 273), lower := (rows 11 162 69 296 82 36 68 128 256), losses := [] }

theorem u4667 : Upper (D 6) (R 6) [10,160,65,288,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4668 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 162 69 296 82 36 80 133 261), lower := (rows 11 162 69 296 82 36 80 128 256), losses := [] }

theorem u4668 : Upper (D 6) (R 6) [10,160,65,288,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4668 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4669 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 146, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 162 69 328 22 36 65 176 304), lower := (rows 11 162 69 328 22 36 65 128 256), losses := [] }

theorem u4669 : Upper (D 6) (R 6) [10,160,65,320,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4670 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 328 22 36 80 161 289), lower := (rows 11 162 69 328 22 36 80 128 256), losses := [] }

theorem u4670 : Upper (D 6) (R 6) [10,160,65,320,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4670 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4671 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 178, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 162 69 328 22 36 96 145 273), lower := (rows 11 162 69 328 22 36 96 128 256), losses := [] }

theorem u4671 : Upper (D 6) (R 6) [10,160,65,320,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4672 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 70 25 52 288 65 196 324), lower := (rows 11 162 70 25 52 288 65 128 256), losses := [] }

theorem u4672 : Upper (D 6) (R 6) [10,160,66,17,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4672 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4673 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 162 70 25 52 288 68 193 321), lower := (rows 11 162 70 25 52 288 68 128 256), losses := [] }

theorem u4673 : Upper (D 6) (R 6) [10,160,66,17,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4673 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4674 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 162 70 25 112 288 65 132 260), lower := (rows 11 162 70 25 112 288 65 128 256), losses := [] }

theorem u4674 : Upper (D 6) (R 6) [10,160,66,17,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4674 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4675 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 162 70 25 112 288 68 133 261), lower := (rows 11 162 70 25 112 288 68 128 256), losses := [] }

theorem u4675 : Upper (D 6) (R 6) [10,160,66,17,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4675 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4676 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 70 25 276 36 65 224 352), lower := (rows 11 162 70 25 276 36 65 128 256), losses := [] }

theorem u4676 : Upper (D 6) (R 6) [10,160,66,17,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4677 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 281, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 25 276 36 96 193 321), lower := (rows 11 162 70 25 276 36 96 128 256), losses := [] }

theorem u4677 : Upper (D 6) (R 6) [10,160,66,17,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4678 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 70 25 276 96 65 164 292), lower := (rows 11 162 70 25 276 96 65 128 256), losses := [] }

theorem u4678 : Upper (D 6) (R 6) [10,160,66,17,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4679 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 162 70 25 276 96 68 161 289), lower := (rows 11 162 70 25 276 96 68 128 256), losses := [] }

theorem u4679 : Upper (D 6) (R 6) [10,160,66,17,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4679
end Delivery.IrregularNine14.P06
