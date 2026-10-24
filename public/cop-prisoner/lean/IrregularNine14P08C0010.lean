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

def b600 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 336 160 96 131 259), lower := (rows 97 7 140 56 336 160 96 128 256), losses := [] }

theorem u600 : Upper (D 8) (R 8) [96,5,136,48,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b601 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 140 296 82 160 65 176 304), lower := (rows 97 7 140 296 82 160 65 128 256), losses := [] }

theorem u601 : Upper (D 8) (R 8) [96,5,136,288,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b602 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 7 140 296 82 160 80 161 289), lower := (rows 97 7 140 296 82 160 80 128 256), losses := [] }

theorem u602 : Upper (D 8) (R 8) [96,5,136,288,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b602 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b603 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 296 82 160 96 145 273), lower := (rows 97 7 140 296 82 160 96 128 256), losses := [] }

theorem u603 : Upper (D 8) (R 8) [96,5,136,288,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b604 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 97 7 268 42 145 160 80 224 352), lower := (rows 97 7 268 42 145 160 80 128 256), losses := [] }

theorem u604 : Upper (D 8) (R 8) [96,5,264,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b604 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b605 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 42 145 160 96 208 336), lower := (rows 97 7 268 42 145 160 96 128 256), losses := [] }

theorem u605 : Upper (D 8) (R 8) [96,5,264,34,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b606 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 42 208 160 65 176 304), lower := (rows 97 7 268 42 208 160 65 128 256), losses := [] }

theorem u606 : Upper (D 8) (R 8) [96,5,264,34,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b607 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 7 268 42 208 160 80 161 289), lower := (rows 97 7 268 42 208 160 80 128 256), losses := [] }

theorem u607 : Upper (D 8) (R 8) [96,5,264,34,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b607 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b608 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 268 42 208 160 96 145 273), lower := (rows 97 7 268 42 208 160 96 128 256), losses := [] }

theorem u608 : Upper (D 8) (R 8) [96,5,264,34,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b609 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 26 56 160 65 192 448), lower := (rows 97 7 292 26 56 160 65 128 256), losses := [] }

theorem u609 : Upper (D 8) (R 8) [96,5,288,18,40,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b610 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 262, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 292 26 56 160 192 193 321), lower := (rows 97 7 292 26 56 160 192 128 256), losses := [] }

theorem u610 : Upper (D 8) (R 8) [96,5,288,18,40,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b611 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 26 208 160 65 168 296), lower := (rows 97 7 292 26 208 160 65 128 256), losses := [] }

theorem u611 : Upper (D 8) (R 8) [96,5,288,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b612 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 7 292 26 208 160 72 161 289), lower := (rows 97 7 292 26 208 160 72 128 256), losses := [] }

theorem u612 : Upper (D 8) (R 8) [96,5,288,18,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b612 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b613 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 26 208 160 96 137 265), lower := (rows 97 7 292 26 208 160 96 128 256), losses := [] }

theorem u613 : Upper (D 8) (R 8) [96,5,288,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b614 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 42 88 160 65 144 400), lower := (rows 97 7 292 42 88 160 65 128 256), losses := [] }

theorem u614 : Upper (D 8) (R 8) [96,5,288,34,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b615 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 7 292 42 88 160 80 129 385), lower := (rows 97 7 292 42 88 160 80 128 256), losses := [] }

theorem u615 : Upper (D 8) (R 8) [96,5,288,34,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b615 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b616 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 292 42 88 160 192 145 273), lower := (rows 97 7 292 42 88 160 192 128 256), losses := [] }

theorem u616 : Upper (D 8) (R 8) [96,5,288,34,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b617 : PairBound 9 := { available := 80, camps := [], pairs := [], upper := (rows 97 7 292 42 145 160 72 208 336), lower := (rows 97 7 292 42 145 160 72 128 256), losses := [] }

theorem u617 : Upper (D 8) (R 8) [96,5,288,34,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b617 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b618 : PairBound 9 := { available := 72, camps := [], pairs := [], upper := (rows 97 7 292 42 145 160 80 200 328), lower := (rows 97 7 292 42 145 160 80 128 256), losses := [] }

theorem u618 : Upper (D 8) (R 8) [96,5,288,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b618 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b619 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 42 152 160 65 208 336), lower := (rows 97 7 292 42 152 160 65 128 256), losses := [] }

theorem u619 : Upper (D 8) (R 8) [96,5,288,34,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b620 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 97 7 292 42 152 160 80 193 321), lower := (rows 97 7 292 42 152 160 80 128 256), losses := [] }

theorem u620 : Upper (D 8) (R 8) [96,5,288,34,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b620 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b621 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 42 208 160 65 152 280), lower := (rows 97 7 292 42 208 160 65 128 256), losses := [] }

theorem u621 : Upper (D 8) (R 8) [96,5,288,34,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b622 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 7 292 42 208 160 72 145 273), lower := (rows 97 7 292 42 208 160 72 128 256), losses := [] }

theorem u622 : Upper (D 8) (R 8) [96,5,288,34,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b622 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b623 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 7 292 42 208 160 80 137 265), lower := (rows 97 7 292 42 208 160 80 128 256), losses := [] }

theorem u623 : Upper (D 8) (R 8) [96,5,288,34,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b623 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b624 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 56 82 160 65 136 392), lower := (rows 97 7 292 56 82 160 65 128 256), losses := [] }

theorem u624 : Upper (D 8) (R 8) [96,5,288,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b625 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 7 292 56 82 160 72 129 385), lower := (rows 97 7 292 56 82 160 72 128 256), losses := [] }

theorem u625 : Upper (D 8) (R 8) [96,5,288,48,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b625 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b626 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 292 56 82 160 192 137 265), lower := (rows 97 7 292 56 82 160 192 128 256), losses := [] }

theorem u626 : Upper (D 8) (R 8) [96,5,288,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b627 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 97 7 292 74 145 160 72 176 304), lower := (rows 97 7 292 74 145 160 72 128 256), losses := [] }

theorem u627 : Upper (D 8) (R 8) [96,5,288,66,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b627 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b628 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 97 7 292 74 145 160 80 168 296), lower := (rows 97 7 292 74 145 160 80 128 256), losses := [] }

theorem u628 : Upper (D 8) (R 8) [96,5,288,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b628 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b629 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 74 145 160 96 152 280), lower := (rows 97 7 292 74 145 160 96 128 256), losses := [] }

theorem u629 : Upper (D 8) (R 8) [96,5,288,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b630 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 292 74 152 160 65 176 304), lower := (rows 97 7 292 74 152 160 65 128 256), losses := [] }

theorem u630 : Upper (D 8) (R 8) [96,5,288,66,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b631 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 7 292 74 152 160 80 161 289), lower := (rows 97 7 292 74 152 160 80 128 256), losses := [] }

theorem u631 : Upper (D 8) (R 8) [96,5,288,66,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b631 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b632 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 74 152 160 96 145 273), lower := (rows 97 7 292 74 152 160 96 128 256), losses := [] }

theorem u632 : Upper (D 8) (R 8) [96,5,288,66,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b633 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 97 7 292 88 145 160 66 168 296), lower := (rows 97 7 292 88 145 160 66 128 256), losses := [] }

theorem u633 : Upper (D 8) (R 8) [96,5,288,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b633 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b634 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 97 7 292 88 145 160 72 162 290), lower := (rows 97 7 292 88 145 160 72 128 256), losses := [] }

theorem u634 : Upper (D 8) (R 8) [96,5,288,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b634 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b635 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 88 145 160 96 138 266), lower := (rows 97 7 292 88 145 160 96 128 256), losses := [] }

theorem u635 : Upper (D 8) (R 8) [96,5,288,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b636 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 88 146 160 65 168 296), lower := (rows 97 7 292 88 146 160 65 128 256), losses := [] }

theorem u636 : Upper (D 8) (R 8) [96,5,288,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b637 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 7 292 88 146 160 72 161 289), lower := (rows 97 7 292 88 146 160 72 128 256), losses := [] }

theorem u637 : Upper (D 8) (R 8) [96,5,288,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b637 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b638 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 88 146 160 96 137 265), lower := (rows 97 7 292 88 146 160 96 128 256), losses := [] }

theorem u638 : Upper (D 8) (R 8) [96,5,288,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b639 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 97 14 38 265 145 160 80 224 352), lower := (rows 97 14 38 265 145 160 80 128 256), losses := [] }

theorem u639 : Upper (D 8) (R 8) [96,12,34,257,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b639 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b640 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 265 145 160 96 208 336), lower := (rows 97 14 38 265 145 160 96 128 256), losses := [] }

theorem u640 : Upper (D 8) (R 8) [96,12,34,257,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b641 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 38 265 208 160 65 176 304), lower := (rows 97 14 38 265 208 160 65 128 256), losses := [] }

theorem u641 : Upper (D 8) (R 8) [96,12,34,257,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b642 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 14 38 265 208 160 80 161 289), lower := (rows 97 14 38 265 208 160 80 128 256), losses := [] }

theorem u642 : Upper (D 8) (R 8) [96,12,34,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b642 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b643 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 97 14 38 265 208 160 96 145 273), lower := (rows 97 14 38 265 208 160 96 128 256), losses := [] }

theorem u643 : Upper (D 8) (R 8) [96,12,34,257,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b644 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 97 14 52 137 273 160 66 224 352), lower := (rows 97 14 52 137 273 160 66 128 256), losses := [] }

theorem u644 : Upper (D 8) (R 8) [96,12,48,129,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b644 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b645 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 273 160 96 194 322), lower := (rows 97 14 52 137 273 160 96 128 256), losses := [] }

theorem u645 : Upper (D 8) (R 8) [96,12,48,129,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b646 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 336 160 65 162 290), lower := (rows 97 14 52 137 336 160 65 128 256), losses := [] }

theorem u646 : Upper (D 8) (R 8) [96,12,48,129,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b647 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 14 52 137 336 160 66 161 289), lower := (rows 97 14 52 137 336 160 66 128 256), losses := [] }

theorem u647 : Upper (D 8) (R 8) [96,12,48,129,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b647 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b648 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 336 160 96 131 259), lower := (rows 97 14 52 137 336 160 96 128 256), losses := [] }

theorem u648 : Upper (D 8) (R 8) [96,12,48,129,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b649 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 200 273 160 65 162 290), lower := (rows 97 14 52 200 273 160 65 128 256), losses := [] }

theorem u649 : Upper (D 8) (R 8) [96,12,48,192,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b650 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 14 52 200 273 160 66 161 289), lower := (rows 97 14 52 200 273 160 66 128 256), losses := [] }

theorem u650 : Upper (D 8) (R 8) [96,12,48,192,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b650 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b651 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 200 273 160 96 131 259), lower := (rows 97 14 52 200 273 160 96 128 256), losses := [] }

theorem u651 : Upper (D 8) (R 8) [96,12,48,192,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b652 : PairBound 9 := { available := 32, camps := [], pairs := [], upper := (rows 97 14 84 137 273 160 66 160 288), lower := (rows 97 14 84 137 273 160 66 128 256), losses := [] }

theorem u652 : Upper (D 8) (R 8) [96,12,80,129,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b652 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b653 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 137 273 160 96 162 290), lower := (rows 97 14 84 137 273 160 96 128 256), losses := [] }

theorem u653 : Upper (D 8) (R 8) [96,12,80,129,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b654 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 432, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 84 137 304 160 65 162 290), lower := (rows 97 14 84 137 304 160 65 128 256), losses := [] }

theorem u654 : Upper (D 8) (R 8) [96,12,80,129,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b655 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 14 84 137 304 160 66 161 289), lower := (rows 97 14 84 137 304 160 66 128 256), losses := [] }

theorem u655 : Upper (D 8) (R 8) [96,12,80,129,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b655 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b656 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 137 304 160 96 131 259), lower := (rows 97 14 84 137 304 160 96 128 256), losses := [] }

theorem u656 : Upper (D 8) (R 8) [96,12,80,129,288,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b657 : PairBound 9 := { available := 32, camps := [], pairs := [], upper := (rows 97 14 84 265 145 160 66 160 288), lower := (rows 97 14 84 265 145 160 66 128 256), losses := [] }

theorem u657 : Upper (D 8) (R 8) [96,12,80,257,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b657 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b658 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 84 265 145 160 96 162 290), lower := (rows 97 14 84 265 145 160 96 128 256), losses := [] }

theorem u658 : Upper (D 8) (R 8) [96,12,80,257,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b659 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 426, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 84 296 145 160 65 162 290), lower := (rows 97 14 84 296 145 160 65 128 256), losses := [] }

theorem u659 : Upper (D 8) (R 8) [96,12,80,288,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u659
end Delivery.IrregularNine14.P08
