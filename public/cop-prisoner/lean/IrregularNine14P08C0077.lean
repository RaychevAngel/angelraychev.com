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

def b4620 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 42 176 96 89 153 281), lower := (rows 97 7 388 42 176 96 64 128 256), losses := [] }

theorem u4620 : Upper (D 8) (R 8) [96,5,384,34,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4621 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 42 208 33 120 184 312), lower := (rows 97 7 388 42 208 33 64 128 256), losses := [] }

theorem u4621 : Upper (D 8) (R 8) [96,5,384,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4622 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 7 388 42 208 40 113 177 305), lower := (rows 97 7 388 42 208 40 64 128 256), losses := [] }

theorem u4622 : Upper (D 8) (R 8) [96,5,384,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4622 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4623 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 7 388 42 208 48 105 169 297), lower := (rows 97 7 388 42 208 48 64 128 256), losses := [] }

theorem u4623 : Upper (D 8) (R 8) [96,5,384,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4623 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4624 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 56 82 33 232 168 424), lower := (rows 97 7 388 56 82 33 64 128 256), losses := [] }

theorem u4624 : Upper (D 8) (R 8) [96,5,384,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4625 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 388 56 82 40 225 161 417), lower := (rows 97 7 388 56 82 40 64 128 256), losses := [] }

theorem u4625 : Upper (D 8) (R 8) [96,5,384,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4625 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4626 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 56 82 160 105 169 297), lower := (rows 97 7 388 56 82 160 64 128 256), losses := [] }

theorem u4626 : Upper (D 8) (R 8) [96,5,384,48,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4627 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 97 7 388 56 145 34 104 232 360), lower := (rows 97 7 388 56 145 34 64 128 256), losses := [] }

theorem u4627 : Upper (D 8) (R 8) [96,5,384,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4627 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4628 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 97 7 388 56 145 40 98 226 354), lower := (rows 97 7 388 56 145 40 64 128 256), losses := [] }

theorem u4628 : Upper (D 8) (R 8) [96,5,384,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4628 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4629 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 56 145 96 106 170 298), lower := (rows 97 7 388 56 145 96 64 128 256), losses := [] }

theorem u4629 : Upper (D 8) (R 8) [96,5,384,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4630 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 56 208 33 106 170 298), lower := (rows 97 7 388 56 208 33 64 128 256), losses := [] }

theorem u4630 : Upper (D 8) (R 8) [96,5,384,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4631 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 7 388 56 208 34 105 169 297), lower := (rows 97 7 388 56 208 34 64 128 256), losses := [] }

theorem u4631 : Upper (D 8) (R 8) [96,5,384,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4631 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4632 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 7 388 56 208 40 99 163 291), lower := (rows 97 7 388 56 208 40 64 128 256), losses := [] }

theorem u4632 : Upper (D 8) (R 8) [96,5,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4632 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4633 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 97 7 388 74 145 40 112 176 304), lower := (rows 97 7 388 74 145 40 64 128 256), losses := [] }

theorem u4633 : Upper (D 8) (R 8) [96,5,384,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4633 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4634 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 97 7 388 74 145 48 104 168 296), lower := (rows 97 7 388 74 145 48 64 128 256), losses := [] }

theorem u4634 : Upper (D 8) (R 8) [96,5,384,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4634 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4635 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 74 176 33 120 184 312), lower := (rows 97 7 388 74 176 33 64 128 256), losses := [] }

theorem u4635 : Upper (D 8) (R 8) [96,5,384,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4636 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 7 388 74 176 40 113 177 305), lower := (rows 97 7 388 74 176 40 64 128 256), losses := [] }

theorem u4636 : Upper (D 8) (R 8) [96,5,384,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4636 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4637 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 7 388 74 176 48 105 169 297), lower := (rows 97 7 388 74 176 48 64 128 256), losses := [] }

theorem u4637 : Upper (D 8) (R 8) [96,5,384,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4637 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4638 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 97 7 388 88 145 34 104 168 296), lower := (rows 97 7 388 88 145 34 64 128 256), losses := [] }

theorem u4638 : Upper (D 8) (R 8) [96,5,384,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4638 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4639 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 97 7 388 88 145 40 98 162 290), lower := (rows 97 7 388 88 145 40 64 128 256), losses := [] }

theorem u4639 : Upper (D 8) (R 8) [96,5,384,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4639 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4640 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 88 176 33 106 170 298), lower := (rows 97 7 388 88 176 33 64 128 256), losses := [] }

theorem u4640 : Upper (D 8) (R 8) [96,5,384,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4641 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 7 388 88 176 34 105 169 297), lower := (rows 97 7 388 88 176 34 64 128 256), losses := [] }

theorem u4641 : Upper (D 8) (R 8) [96,5,384,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4641 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4642 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 7 388 88 176 40 99 163 291), lower := (rows 97 7 388 88 176 40 64 128 256), losses := [] }

theorem u4642 : Upper (D 8) (R 8) [96,5,384,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4642 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4643 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 22 137 273 96 224 160 416), lower := (rows 97 14 22 137 273 96 64 128 256), losses := [] }

theorem u4643 : Upper (D 8) (R 8) [96,12,18,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4644 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 22 137 273 160 96 224 352), lower := (rows 97 14 22 137 273 160 64 128 256), losses := [] }

theorem u4644 : Upper (D 8) (R 8) [96,12,18,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4645 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 22 137 304 33 224 224 480), lower := (rows 97 14 22 137 304 33 64 128 256), losses := [] }

theorem u4645 : Upper (D 8) (R 8) [96,12,18,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4646 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 22 137 304 96 225 161 417), lower := (rows 97 14 22 137 304 96 64 128 256), losses := [] }

theorem u4646 : Upper (D 8) (R 8) [96,12,18,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4647 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 22 137 304 160 97 225 353), lower := (rows 97 14 22 137 304 160 64 128 256), losses := [] }

theorem u4647 : Upper (D 8) (R 8) [96,12,18,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4648 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 136, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 22 168 273 33 224 224 480), lower := (rows 97 14 22 168 273 33 64 128 256), losses := [] }

theorem u4648 : Upper (D 8) (R 8) [96,12,18,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4649 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 22 168 273 96 225 161 417), lower := (rows 97 14 22 168 273 96 64 128 256), losses := [] }

theorem u4649 : Upper (D 8) (R 8) [96,12,18,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4650 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 22 168 273 160 97 225 353), lower := (rows 97 14 22 168 273 160 64 128 256), losses := [] }

theorem u4650 : Upper (D 8) (R 8) [96,12,18,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4650 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4651 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 22 168 304 33 193 193 449), lower := (rows 97 14 22 168 304 33 64 128 256), losses := [] }

theorem u4651 : Upper (D 8) (R 8) [96,12,18,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4652 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 22 168 304 96 193 129 385), lower := (rows 97 14 22 168 304 96 64 128 256), losses := [] }

theorem u4652 : Upper (D 8) (R 8) [96,12,18,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4653 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 22 168 304 160 65 193 321), lower := (rows 97 14 22 168 304 160 64 128 256), losses := [] }

theorem u4653 : Upper (D 8) (R 8) [96,12,18,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4654 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 14 38 137 273 48 224 224 480), lower := (rows 97 14 38 137 273 48 64 128 256), losses := [] }

theorem u4654 : Upper (D 8) (R 8) [96,12,34,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4654 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4655 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 137 273 96 240 176 432), lower := (rows 97 14 38 137 273 96 64 128 256), losses := [] }

theorem u4655 : Upper (D 8) (R 8) [96,12,34,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4656 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 137 273 160 112 240 368), lower := (rows 97 14 38 137 273 160 64 128 256), losses := [] }

theorem u4656 : Upper (D 8) (R 8) [96,12,34,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4657 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 137 304 33 208 208 464), lower := (rows 97 14 38 137 304 33 64 128 256), losses := [] }

theorem u4657 : Upper (D 8) (R 8) [96,12,34,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4658 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 14 38 137 304 48 193 193 449), lower := (rows 97 14 38 137 304 48 64 128 256), losses := [] }

theorem u4658 : Upper (D 8) (R 8) [96,12,34,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4658 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4659 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 137 304 96 209 145 401), lower := (rows 97 14 38 137 304 96 64 128 256), losses := [] }

theorem u4659 : Upper (D 8) (R 8) [96,12,34,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4660 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 137 304 160 81 209 337), lower := (rows 97 14 38 137 304 160 64 128 256), losses := [] }

theorem u4660 : Upper (D 8) (R 8) [96,12,34,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4661 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 137 336 33 240 176 432), lower := (rows 97 14 38 137 336 33 64 128 256), losses := [] }

theorem u4661 : Upper (D 8) (R 8) [96,12,34,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4662 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 38 137 336 48 225 161 417), lower := (rows 97 14 38 137 336 48 64 128 256), losses := [] }

theorem u4662 : Upper (D 8) (R 8) [96,12,34,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4662 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4663 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 137 336 160 113 177 305), lower := (rows 97 14 38 137 336 160 64 128 256), losses := [] }

theorem u4663 : Upper (D 8) (R 8) [96,12,34,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4663 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4664 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 152 273 33 224 224 480), lower := (rows 97 14 38 152 273 33 64 128 256), losses := [] }

theorem u4664 : Upper (D 8) (R 8) [96,12,34,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4665 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 152 273 96 225 161 417), lower := (rows 97 14 38 152 273 96 64 128 256), losses := [] }

theorem u4665 : Upper (D 8) (R 8) [96,12,34,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4665 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4666 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 152 273 160 97 225 353), lower := (rows 97 14 38 152 273 160 64 128 256), losses := [] }

theorem u4666 : Upper (D 8) (R 8) [96,12,34,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4666 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4667 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 152 304 33 193 193 449), lower := (rows 97 14 38 152 304 33 64 128 256), losses := [] }

theorem u4667 : Upper (D 8) (R 8) [96,12,34,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4668 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 152 304 96 193 129 385), lower := (rows 97 14 38 152 304 96 64 128 256), losses := [] }

theorem u4668 : Upper (D 8) (R 8) [96,12,34,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4668 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4669 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 152 304 160 65 193 321), lower := (rows 97 14 38 152 304 160 64 128 256), losses := [] }

theorem u4669 : Upper (D 8) (R 8) [96,12,34,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4670 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 152 336 33 225 161 417), lower := (rows 97 14 38 152 336 33 64 128 256), losses := [] }

theorem u4670 : Upper (D 8) (R 8) [96,12,34,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4671 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 152 336 160 97 161 289), lower := (rows 97 14 38 152 336 160 64 128 256), losses := [] }

theorem u4671 : Upper (D 8) (R 8) [96,12,34,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4672 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 14 38 265 145 48 224 224 480), lower := (rows 97 14 38 265 145 48 64 128 256), losses := [] }

theorem u4672 : Upper (D 8) (R 8) [96,12,34,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4672 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4673 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 265 145 96 240 176 432), lower := (rows 97 14 38 265 145 96 64 128 256), losses := [] }

theorem u4673 : Upper (D 8) (R 8) [96,12,34,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4674 : Route 9 := (fun mask => (mask,id))

def c4674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4674 : Upper (D 8) (R 8) [96,12,34,257,129,128] 13 := by
  apply FastRouting.sound _ _ [96,12,34,257,129,128] 13 (by decide) (choices 1) [16,32] r4674 c4674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u639
  · exact u640

def b4675 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 265 176 33 208 208 464), lower := (rows 97 14 38 265 176 33 64 128 256), losses := [] }

theorem u4675 : Upper (D 8) (R 8) [96,12,34,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4676 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 14 38 265 176 48 193 193 449), lower := (rows 97 14 38 265 176 48 64 128 256), losses := [] }

theorem u4676 : Upper (D 8) (R 8) [96,12,34,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4676 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4677 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 265 176 96 209 145 401), lower := (rows 97 14 38 265 176 96 64 128 256), losses := [] }

theorem u4677 : Upper (D 8) (R 8) [96,12,34,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4678 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 265 176 160 81 209 337), lower := (rows 97 14 38 265 176 160 64 128 256), losses := [] }

theorem u4678 : Upper (D 8) (R 8) [96,12,34,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4679 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 38 265 208 33 240 176 432), lower := (rows 97 14 38 265 208 33 64 128 256), losses := [] }

theorem u4679 : Upper (D 8) (R 8) [96,12,34,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4679
end Delivery.IrregularNine14.P08
