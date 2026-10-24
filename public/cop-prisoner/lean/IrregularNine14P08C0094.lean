import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5640 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 328 148 33 114 178 306), lower := (rows 193 35 44 328 148 33 64 128 256), losses := [] }

theorem u5640 : Upper (D 8) (R 8) [192,33,40,320,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5641 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 35 44 328 148 34 113 177 305), lower := (rows 193 35 44 328 148 34 64 128 256), losses := [] }

theorem u5641 : Upper (D 8) (R 8) [192,33,40,320,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5641 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5642 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 35 44 328 148 48 99 163 291), lower := (rows 193 35 44 328 148 48 64 128 256), losses := [] }

theorem u5642 : Upper (D 8) (R 8) [192,33,40,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5642 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5643 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 328 176 33 86 150 278), lower := (rows 193 35 44 328 176 33 64 128 256), losses := [] }

theorem u5643 : Upper (D 8) (R 8) [192,33,40,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5644 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 193 35 44 328 176 34 85 149 277), lower := (rows 193 35 44 328 176 34 64 128 256), losses := [] }

theorem u5644 : Upper (D 8) (R 8) [192,33,40,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5644 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5645 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 193 35 44 328 176 36 83 147 275), lower := (rows 193 35 44 328 176 36 64 128 256), losses := [] }

theorem u5645 : Upper (D 8) (R 8) [192,33,40,320,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5645 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5646 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 193 35 44 328 176 48 71 135 263), lower := (rows 193 35 44 328 176 48 64 128 256), losses := [] }

theorem u5646 : Upper (D 8) (R 8) [192,33,40,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5646 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5647 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 193 35 70 140 273 40 112 176 304), lower := (rows 193 35 70 140 273 40 64 128 256), losses := [] }

theorem u5647 : Upper (D 8) (R 8) [192,33,66,132,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5647 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5648 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 193 35 70 140 273 48 104 168 296), lower := (rows 193 35 70 140 273 48 64 128 256), losses := [] }

theorem u5648 : Upper (D 8) (R 8) [192,33,66,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5648 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5649 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 70 140 280 33 112 176 304), lower := (rows 193 35 70 140 280 33 64 128 256), losses := [] }

theorem u5649 : Upper (D 8) (R 8) [192,33,66,132,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5650 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 35 70 140 280 48 97 161 289), lower := (rows 193 35 70 140 280 48 64 128 256), losses := [] }

theorem u5650 : Upper (D 8) (R 8) [192,33,66,132,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5650 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5651 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 70 140 304 33 120 184 312), lower := (rows 193 35 70 140 304 33 64 128 256), losses := [] }

theorem u5651 : Upper (D 8) (R 8) [192,33,66,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5652 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 35 70 140 304 40 113 177 305), lower := (rows 193 35 70 140 304 40 64 128 256), losses := [] }

theorem u5652 : Upper (D 8) (R 8) [192,33,66,132,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5652 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5653 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 193 35 70 140 304 48 105 169 297), lower := (rows 193 35 70 140 304 48 64 128 256), losses := [] }

theorem u5653 : Upper (D 8) (R 8) [192,33,66,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5653 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5654 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 193 35 70 152 273 36 104 168 296), lower := (rows 193 35 70 152 273 36 64 128 256), losses := [] }

theorem u5654 : Upper (D 8) (R 8) [192,33,66,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5654 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5655 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 193 35 70 152 273 40 100 164 292), lower := (rows 193 35 70 152 273 40 64 128 256), losses := [] }

theorem u5655 : Upper (D 8) (R 8) [192,33,66,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5655 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5656 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 70 152 276 33 104 168 296), lower := (rows 193 35 70 152 276 33 64 128 256), losses := [] }

theorem u5656 : Upper (D 8) (R 8) [192,33,66,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5657 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 35 70 152 276 40 97 161 289), lower := (rows 193 35 70 152 276 40 64 128 256), losses := [] }

theorem u5657 : Upper (D 8) (R 8) [192,33,66,144,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5657 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5658 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 70 152 304 33 108 172 300), lower := (rows 193 35 70 152 304 33 64 128 256), losses := [] }

theorem u5658 : Upper (D 8) (R 8) [192,33,66,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5659 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 193 35 70 152 304 36 105 169 297), lower := (rows 193 35 70 152 304 36 64 128 256), losses := [] }

theorem u5659 : Upper (D 8) (R 8) [192,33,66,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5659 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5660 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 193 35 70 152 304 40 101 165 293), lower := (rows 193 35 70 152 304 40 64 128 256), losses := [] }

theorem u5660 : Upper (D 8) (R 8) [192,33,66,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5660 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5661 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 193 35 70 168 273 36 120 184 312), lower := (rows 193 35 70 168 273 36 64 128 256), losses := [] }

theorem u5661 : Upper (D 8) (R 8) [192,33,66,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5661 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5662 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 193 35 70 168 273 40 116 180 308), lower := (rows 193 35 70 168 273 40 64 128 256), losses := [] }

theorem u5662 : Upper (D 8) (R 8) [192,33,66,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5662 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5663 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 193 35 70 168 273 48 108 172 300), lower := (rows 193 35 70 168 273 48 64 128 256), losses := [] }

theorem u5663 : Upper (D 8) (R 8) [192,33,66,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5663 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5664 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 70 168 276 33 120 184 312), lower := (rows 193 35 70 168 276 33 64 128 256), losses := [] }

theorem u5664 : Upper (D 8) (R 8) [192,33,66,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5665 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 35 70 168 276 40 113 177 305), lower := (rows 193 35 70 168 276 40 64 128 256), losses := [] }

theorem u5665 : Upper (D 8) (R 8) [192,33,66,160,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5665 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5666 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 193 35 70 168 276 48 105 169 297), lower := (rows 193 35 70 168 276 48 64 128 256), losses := [] }

theorem u5666 : Upper (D 8) (R 8) [192,33,66,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5666 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5667 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 70 168 280 33 116 180 308), lower := (rows 193 35 70 168 280 33 64 128 256), losses := [] }

theorem u5667 : Upper (D 8) (R 8) [192,33,66,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5668 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 35 70 168 280 36 113 177 305), lower := (rows 193 35 70 168 280 36 64 128 256), losses := [] }

theorem u5668 : Upper (D 8) (R 8) [192,33,66,160,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5668 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5669 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 193 35 70 168 280 48 101 165 293), lower := (rows 193 35 70 168 280 48 64 128 256), losses := [] }

theorem u5669 : Upper (D 8) (R 8) [192,33,66,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5669 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5670 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 70 168 304 33 92 156 284), lower := (rows 193 35 70 168 304 33 64 128 256), losses := [] }

theorem u5670 : Upper (D 8) (R 8) [192,33,66,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5671 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 193 35 70 168 304 36 89 153 281), lower := (rows 193 35 70 168 304 36 64 128 256), losses := [] }

theorem u5671 : Upper (D 8) (R 8) [192,33,66,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5671 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5672 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 193 35 70 168 304 40 85 149 277), lower := (rows 193 35 70 168 304 40 64 128 256), losses := [] }

theorem u5672 : Upper (D 8) (R 8) [192,33,66,160,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5672 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5673 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 193 35 70 168 304 48 77 141 269), lower := (rows 193 35 70 168 304 48 64 128 256), losses := [] }

theorem u5673 : Upper (D 8) (R 8) [192,33,66,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5673 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5674 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 193 35 76 152 273 34 100 164 292), lower := (rows 193 35 76 152 273 34 64 128 256), losses := [] }

theorem u5674 : Upper (D 8) (R 8) [192,33,72,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5674 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5675 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 193 35 76 152 273 36 98 162 290), lower := (rows 193 35 76 152 273 36 64 128 256), losses := [] }

theorem u5675 : Upper (D 8) (R 8) [192,33,72,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5675 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5676 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 76 152 274 33 100 164 292), lower := (rows 193 35 76 152 274 33 64 128 256), losses := [] }

theorem u5676 : Upper (D 8) (R 8) [192,33,72,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5677 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 35 76 152 274 36 97 161 289), lower := (rows 193 35 76 152 274 36 64 128 256), losses := [] }

theorem u5677 : Upper (D 8) (R 8) [192,33,72,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5677 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5678 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 76 152 304 33 102 166 294), lower := (rows 193 35 76 152 304 33 64 128 256), losses := [] }

theorem u5678 : Upper (D 8) (R 8) [192,33,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5679 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 193 35 76 152 304 34 101 165 293), lower := (rows 193 35 76 152 304 34 64 128 256), losses := [] }

theorem u5679 : Upper (D 8) (R 8) [192,33,72,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5679 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5680 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 35 76 152 304 36 99 163 291), lower := (rows 193 35 76 152 304 36 64 128 256), losses := [] }

theorem u5680 : Upper (D 8) (R 8) [192,33,72,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5680 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5681 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 193 35 76 168 273 34 116 180 308), lower := (rows 193 35 76 168 273 34 64 128 256), losses := [] }

theorem u5681 : Upper (D 8) (R 8) [192,33,72,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5681 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5682 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 193 35 76 168 273 36 114 178 306), lower := (rows 193 35 76 168 273 36 64 128 256), losses := [] }

theorem u5682 : Upper (D 8) (R 8) [192,33,72,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5682 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5683 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 193 35 76 168 273 48 102 166 294), lower := (rows 193 35 76 168 273 48 64 128 256), losses := [] }

theorem u5683 : Upper (D 8) (R 8) [192,33,72,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5683 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5684 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 76 168 274 33 116 180 308), lower := (rows 193 35 76 168 274 33 64 128 256), losses := [] }

theorem u5684 : Upper (D 8) (R 8) [192,33,72,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5685 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 35 76 168 274 36 113 177 305), lower := (rows 193 35 76 168 274 36 64 128 256), losses := [] }

theorem u5685 : Upper (D 8) (R 8) [192,33,72,160,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5685 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5686 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 193 35 76 168 274 48 101 165 293), lower := (rows 193 35 76 168 274 48 64 128 256), losses := [] }

theorem u5686 : Upper (D 8) (R 8) [192,33,72,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5686 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5687 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 76 168 276 33 114 178 306), lower := (rows 193 35 76 168 276 33 64 128 256), losses := [] }

theorem u5687 : Upper (D 8) (R 8) [192,33,72,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5688 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 35 76 168 276 34 113 177 305), lower := (rows 193 35 76 168 276 34 64 128 256), losses := [] }

theorem u5688 : Upper (D 8) (R 8) [192,33,72,160,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5688 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5689 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 35 76 168 276 48 99 163 291), lower := (rows 193 35 76 168 276 48 64 128 256), losses := [] }

theorem u5689 : Upper (D 8) (R 8) [192,33,72,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5689 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5690 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 76 168 304 33 86 150 278), lower := (rows 193 35 76 168 304 33 64 128 256), losses := [] }

theorem u5690 : Upper (D 8) (R 8) [192,33,72,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5691 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 193 35 76 168 304 34 85 149 277), lower := (rows 193 35 76 168 304 34 64 128 256), losses := [] }

theorem u5691 : Upper (D 8) (R 8) [192,33,72,160,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5691 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5692 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 193 35 76 168 304 36 83 147 275), lower := (rows 193 35 76 168 304 36 64 128 256), losses := [] }

theorem u5692 : Upper (D 8) (R 8) [192,33,72,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5692 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5693 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 193 35 76 168 304 48 71 135 263), lower := (rows 193 35 76 168 304 48 64 128 256), losses := [] }

theorem u5693 : Upper (D 8) (R 8) [192,33,72,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5693 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5694 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 193 35 76 265 176 34 116 180 308), lower := (rows 193 35 76 265 176 34 64 128 256), losses := [] }

theorem u5694 : Upper (D 8) (R 8) [192,33,72,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5694 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5695 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 193 35 76 265 176 36 114 178 306), lower := (rows 193 35 76 265 176 36 64 128 256), losses := [] }

theorem u5695 : Upper (D 8) (R 8) [192,33,72,257,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5695 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5696 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 193 35 76 265 176 48 102 166 294), lower := (rows 193 35 76 265 176 48 64 128 256), losses := [] }

theorem u5696 : Upper (D 8) (R 8) [192,33,72,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5696 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5697 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 76 266 176 33 116 180 308), lower := (rows 193 35 76 266 176 33 64 128 256), losses := [] }

theorem u5697 : Upper (D 8) (R 8) [192,33,72,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5698 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 35 76 266 176 36 113 177 305), lower := (rows 193 35 76 266 176 36 64 128 256), losses := [] }

theorem u5698 : Upper (D 8) (R 8) [192,33,72,258,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5698 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5699 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 193 35 76 266 176 48 101 165 293), lower := (rows 193 35 76 266 176 48 64 128 256), losses := [] }

theorem u5699 : Upper (D 8) (R 8) [192,33,72,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5699 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5699
end Delivery.IrregularNine14.P08
