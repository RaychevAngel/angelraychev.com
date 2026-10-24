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

def b5580 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 193 35 44 74 304 36 209 145 401), lower := (rows 193 35 44 74 304 36 64 128 256), losses := [] }

theorem u5580 : Upper (D 8) (R 8) [192,33,40,66,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5580 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5581 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 193 35 44 74 304 48 197 133 389), lower := (rows 193 35 44 74 304 48 64 128 256), losses := [] }

theorem u5581 : Upper (D 8) (R 8) [192,33,40,66,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5581 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5582 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 74 304 160 85 149 277), lower := (rows 193 35 44 74 304 160 64 128 256), losses := [] }

theorem u5582 : Upper (D 8) (R 8) [192,33,40,66,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5583 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 193 35 44 74 400 33 116 180 308), lower := (rows 193 35 44 74 400 33 64 128 256), losses := [] }

theorem u5583 : Upper (D 8) (R 8) [192,33,40,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5584 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 35 44 74 400 36 113 177 305), lower := (rows 193 35 44 74 400 36 64 128 256), losses := [] }

theorem u5584 : Upper (D 8) (R 8) [192,33,40,66,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5584 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5585 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 193 35 44 74 400 48 101 165 293), lower := (rows 193 35 44 74 400 48 64 128 256), losses := [] }

theorem u5585 : Upper (D 8) (R 8) [192,33,40,66,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5585 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5586 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 88 146 33 356 420 292), lower := (rows 193 35 44 88 146 33 64 128 256), losses := [] }

theorem u5586 : Upper (D 8) (R 8) [192,33,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5587 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 193 35 44 88 146 36 353 417 289), lower := (rows 193 35 44 88 146 36 64 128 256), losses := [] }

theorem u5587 : Upper (D 8) (R 8) [192,33,40,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5587 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5588 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 193 35 44 88 146 288 101 165 293), lower := (rows 193 35 44 88 146 288 64 128 256), losses := [] }

theorem u5588 : Upper (D 8) (R 8) [192,33,40,80,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5588 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5589 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 88 176 33 326 390 262), lower := (rows 193 35 44 88 176 33 64 128 256), losses := [] }

theorem u5589 : Upper (D 8) (R 8) [192,33,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5590 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 193 35 44 88 176 34 325 389 261), lower := (rows 193 35 44 88 176 34 64 128 256), losses := [] }

theorem u5590 : Upper (D 8) (R 8) [192,33,40,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5590 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5591 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 193 35 44 88 176 36 323 387 259), lower := (rows 193 35 44 88 176 36 64 128 256), losses := [] }

theorem u5591 : Upper (D 8) (R 8) [192,33,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5591 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5592 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 193 35 44 88 176 288 71 135 263), lower := (rows 193 35 44 88 176 288 64 128 256), losses := [] }

theorem u5592 : Upper (D 8) (R 8) [192,33,40,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5592 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5593 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 193 35 44 88 273 34 228 164 420), lower := (rows 193 35 44 88 273 34 64 128 256), losses := [] }

theorem u5593 : Upper (D 8) (R 8) [192,33,40,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5593 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5594 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 193 35 44 88 273 36 226 162 418), lower := (rows 193 35 44 88 273 36 64 128 256), losses := [] }

theorem u5594 : Upper (D 8) (R 8) [192,33,40,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5594 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5595 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 88 273 160 102 166 294), lower := (rows 193 35 44 88 273 160 64 128 256), losses := [] }

theorem u5595 : Upper (D 8) (R 8) [192,33,40,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5596 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 88 274 33 228 164 420), lower := (rows 193 35 44 88 274 33 64 128 256), losses := [] }

theorem u5596 : Upper (D 8) (R 8) [192,33,40,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5597 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 35 44 88 274 36 225 161 417), lower := (rows 193 35 44 88 274 36 64 128 256), losses := [] }

theorem u5597 : Upper (D 8) (R 8) [192,33,40,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5597 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5598 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 88 274 160 101 165 293), lower := (rows 193 35 44 88 274 160 64 128 256), losses := [] }

theorem u5598 : Upper (D 8) (R 8) [192,33,40,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5599 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 88 304 33 198 134 390), lower := (rows 193 35 44 88 304 33 64 128 256), losses := [] }

theorem u5599 : Upper (D 8) (R 8) [192,33,40,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5600 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 193 35 44 88 304 34 197 133 389), lower := (rows 193 35 44 88 304 34 64 128 256), losses := [] }

theorem u5600 : Upper (D 8) (R 8) [192,33,40,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5600 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5601 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 193 35 44 88 304 36 195 131 387), lower := (rows 193 35 44 88 304 36 64 128 256), losses := [] }

theorem u5601 : Upper (D 8) (R 8) [192,33,40,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5601 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5602 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 88 304 160 71 135 263), lower := (rows 193 35 44 88 304 160 64 128 256), losses := [] }

theorem u5602 : Upper (D 8) (R 8) [192,33,40,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5603 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 88 400 33 102 166 294), lower := (rows 193 35 44 88 400 33 64 128 256), losses := [] }

theorem u5603 : Upper (D 8) (R 8) [192,33,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5604 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 193 35 44 88 400 34 101 165 293), lower := (rows 193 35 44 88 400 34 64 128 256), losses := [] }

theorem u5604 : Upper (D 8) (R 8) [192,33,40,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5604 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5605 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 35 44 88 400 36 99 163 291), lower := (rows 193 35 44 88 400 36 64 128 256), losses := [] }

theorem u5605 : Upper (D 8) (R 8) [192,33,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5605 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5606 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 193 35 44 265 82 36 240 176 432), lower := (rows 193 35 44 265 82 36 64 128 256), losses := [] }

theorem u5606 : Upper (D 8) (R 8) [192,33,40,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5606 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5607 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 193 35 44 265 82 48 228 164 420), lower := (rows 193 35 44 265 82 48 64 128 256), losses := [] }

theorem u5607 : Upper (D 8) (R 8) [192,33,40,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5607 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5608 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 265 82 160 116 180 308), lower := (rows 193 35 44 265 82 160 64 128 256), losses := [] }

theorem u5608 : Upper (D 8) (R 8) [192,33,40,257,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5609 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 193 35 44 265 84 34 240 176 432), lower := (rows 193 35 44 265 84 34 64 128 256), losses := [] }

theorem u5609 : Upper (D 8) (R 8) [192,33,40,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5609 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5610 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 193 35 44 265 84 48 226 162 418), lower := (rows 193 35 44 265 84 48 64 128 256), losses := [] }

theorem u5610 : Upper (D 8) (R 8) [192,33,40,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5610 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5611 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 265 84 160 114 178 306), lower := (rows 193 35 44 265 84 160 64 128 256), losses := [] }

theorem u5611 : Upper (D 8) (R 8) [192,33,40,257,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5612 : PairBound 9 := { available := 148, camps := [], pairs := [], upper := (rows 193 35 44 265 112 34 212 148 404), lower := (rows 193 35 44 265 112 34 64 128 256), losses := [] }

theorem u5612 : Upper (D 8) (R 8) [192,33,40,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5612 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5613 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 193 35 44 265 112 36 210 146 402), lower := (rows 193 35 44 265 112 36 64 128 256), losses := [] }

theorem u5613 : Upper (D 8) (R 8) [192,33,40,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5613 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5614 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 193 35 44 265 112 48 198 134 390), lower := (rows 193 35 44 265 112 48 64 128 256), losses := [] }

theorem u5614 : Upper (D 8) (R 8) [192,33,40,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5614 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5615 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 265 112 160 86 150 278), lower := (rows 193 35 44 265 112 160 64 128 256), losses := [] }

theorem u5615 : Upper (D 8) (R 8) [192,33,40,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5615 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5616 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 266 84 33 240 176 432), lower := (rows 193 35 44 266 84 33 64 128 256), losses := [] }

theorem u5616 : Upper (D 8) (R 8) [192,33,40,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5617 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 35 44 266 84 48 225 161 417), lower := (rows 193 35 44 266 84 48 64 128 256), losses := [] }

theorem u5617 : Upper (D 8) (R 8) [192,33,40,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5617 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5618 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 266 84 160 113 177 305), lower := (rows 193 35 44 266 84 160 64 128 256), losses := [] }

theorem u5618 : Upper (D 8) (R 8) [192,33,40,258,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5619 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 266 112 33 212 148 404), lower := (rows 193 35 44 266 112 33 64 128 256), losses := [] }

theorem u5619 : Upper (D 8) (R 8) [192,33,40,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5620 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 193 35 44 266 112 36 209 145 401), lower := (rows 193 35 44 266 112 36 64 128 256), losses := [] }

theorem u5620 : Upper (D 8) (R 8) [192,33,40,258,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5620 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5621 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 193 35 44 266 112 48 197 133 389), lower := (rows 193 35 44 266 112 48 64 128 256), losses := [] }

theorem u5621 : Upper (D 8) (R 8) [192,33,40,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5621 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5622 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 266 112 160 85 149 277), lower := (rows 193 35 44 266 112 160 64 128 256), losses := [] }

theorem u5622 : Upper (D 8) (R 8) [192,33,40,258,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5623 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 268 82 33 240 176 432), lower := (rows 193 35 44 268 82 33 64 128 256), losses := [] }

theorem u5623 : Upper (D 8) (R 8) [192,33,40,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5624 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 35 44 268 82 48 225 161 417), lower := (rows 193 35 44 268 82 48 64 128 256), losses := [] }

theorem u5624 : Upper (D 8) (R 8) [192,33,40,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5624 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5625 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 268 82 160 113 177 305), lower := (rows 193 35 44 268 82 160 64 128 256), losses := [] }

theorem u5625 : Upper (D 8) (R 8) [192,33,40,260,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5626 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 268 112 33 210 146 402), lower := (rows 193 35 44 268 112 33 64 128 256), losses := [] }

theorem u5626 : Upper (D 8) (R 8) [192,33,40,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5627 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 193 35 44 268 112 34 209 145 401), lower := (rows 193 35 44 268 112 34 64 128 256), losses := [] }

theorem u5627 : Upper (D 8) (R 8) [192,33,40,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5627 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5628 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 193 35 44 268 112 48 195 131 387), lower := (rows 193 35 44 268 112 48 64 128 256), losses := [] }

theorem u5628 : Upper (D 8) (R 8) [192,33,40,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5628 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5629 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 268 112 160 83 147 275), lower := (rows 193 35 44 268 112 160 64 128 256), losses := [] }

theorem u5629 : Upper (D 8) (R 8) [192,33,40,260,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5630 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 280 82 33 228 164 420), lower := (rows 193 35 44 280 82 33 64 128 256), losses := [] }

theorem u5630 : Upper (D 8) (R 8) [192,33,40,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5631 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 35 44 280 82 36 225 161 417), lower := (rows 193 35 44 280 82 36 64 128 256), losses := [] }

theorem u5631 : Upper (D 8) (R 8) [192,33,40,272,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5631 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5632 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 280 82 160 101 165 293), lower := (rows 193 35 44 280 82 160 64 128 256), losses := [] }

theorem u5632 : Upper (D 8) (R 8) [192,33,40,272,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5633 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 280 112 33 198 134 390), lower := (rows 193 35 44 280 112 33 64 128 256), losses := [] }

theorem u5633 : Upper (D 8) (R 8) [192,33,40,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5634 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 193 35 44 280 112 34 197 133 389), lower := (rows 193 35 44 280 112 34 64 128 256), losses := [] }

theorem u5634 : Upper (D 8) (R 8) [192,33,40,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5634 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5635 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 193 35 44 280 112 36 195 131 387), lower := (rows 193 35 44 280 112 36 64 128 256), losses := [] }

theorem u5635 : Upper (D 8) (R 8) [192,33,40,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5635 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5636 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 280 112 160 71 135 263), lower := (rows 193 35 44 280 112 160 64 128 256), losses := [] }

theorem u5636 : Upper (D 8) (R 8) [192,33,40,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5637 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 328 146 33 116 180 308), lower := (rows 193 35 44 328 146 33 64 128 256), losses := [] }

theorem u5637 : Upper (D 8) (R 8) [192,33,40,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5638 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 35 44 328 146 36 113 177 305), lower := (rows 193 35 44 328 146 36 64 128 256), losses := [] }

theorem u5638 : Upper (D 8) (R 8) [192,33,40,320,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5638 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5639 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 193 35 44 328 146 48 101 165 293), lower := (rows 193 35 44 328 146 48 64 128 256), losses := [] }

theorem u5639 : Upper (D 8) (R 8) [192,33,40,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5639 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5639
end Delivery.IrregularNine14.P08
