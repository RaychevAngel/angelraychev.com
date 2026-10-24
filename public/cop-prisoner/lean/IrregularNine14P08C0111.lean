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

def b6660 : PairBound 9 := { available := 161, camps := [], pairs := [(4,0)], upper := (rows 321 7 44 152 50 96 225 161 417), lower := (rows 321 7 44 152 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 97 64 128 256), good := (rows 352 54 44 152 50 96 96 128 256) }] }

theorem u6660 : Upper (D 8) (R 8) [320,5,40,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6661 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 152 50 160 97 225 353), lower := (rows 321 7 44 152 50 160 64 128 256), losses := [] }

theorem u6661 : Upper (D 8) (R 8) [320,5,40,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6662 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 321 7 44 152 112 33 226 162 418), lower := (rows 321 7 44 152 112 33 64 128 256), losses := [] }

theorem u6662 : Upper (D 8) (R 8) [320,5,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6663 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 7 44 152 112 34 225 161 417), lower := (rows 321 7 44 152 112 34 64 128 256), losses := [] }

theorem u6663 : Upper (D 8) (R 8) [320,5,40,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6663 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6664 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 152 112 160 99 163 291), lower := (rows 321 7 44 152 112 160 64 128 256), losses := [] }

theorem u6664 : Upper (D 8) (R 8) [320,5,40,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6665 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 321 7 140 42 49 48 224 224 480), lower := (rows 321 7 140 42 49 48 64 128 256), losses := [] }

theorem u6665 : Upper (D 8) (R 8) [320,5,136,34,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6665 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6666 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 142, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 140 42 49 96 240 176 432), lower := (rows 321 7 140 42 49 96 64 128 256), losses := [] }

theorem u6666 : Upper (D 8) (R 8) [320,5,136,34,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6666 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6667 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 42 49 160 112 240 368), lower := (rows 321 7 140 42 49 160 64 128 256), losses := [] }

theorem u6667 : Upper (D 8) (R 8) [320,5,136,34,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6668 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 140 42 112 33 240 176 432), lower := (rows 321 7 140 42 112 33 64 128 256), losses := [] }

theorem u6668 : Upper (D 8) (R 8) [320,5,136,34,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6668 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6669 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 7 140 42 112 48 225 161 417), lower := (rows 321 7 140 42 112 48 64 128 256), losses := [] }

theorem u6669 : Upper (D 8) (R 8) [320,5,136,34,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6669 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6670 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 42 112 160 113 177 305), lower := (rows 321 7 140 42 112 160 64 128 256), losses := [] }

theorem u6670 : Upper (D 8) (R 8) [320,5,136,34,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6671 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 164 26 56 33 224 224 480), lower := (rows 321 7 164 26 56 33 64 128 256), losses := [] }

theorem u6671 : Upper (D 8) (R 8) [320,5,160,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6672 : PairBound 9 := { available := 161, camps := [], pairs := [(3,0)], upper := (rows 321 7 164 26 56 96 225 161 417), lower := (rows 321 7 164 26 56 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 97 64 128 256), good := (rows 352 62 164 26 56 96 96 128 256) }] }

theorem u6672 : Upper (D 8) (R 8) [320,5,160,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6673 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 26 56 160 97 225 353), lower := (rows 321 7 164 26 56 160 64 128 256), losses := [] }

theorem u6673 : Upper (D 8) (R 8) [320,5,160,18,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6674 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 321 7 164 26 112 33 232 168 424), lower := (rows 321 7 164 26 112 33 64 128 256), losses := [] }

theorem u6674 : Upper (D 8) (R 8) [320,5,160,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6675 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 7 164 26 112 40 225 161 417), lower := (rows 321 7 164 26 112 40 64 128 256), losses := [] }

theorem u6675 : Upper (D 8) (R 8) [320,5,160,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6675 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6676 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 26 112 160 105 169 297), lower := (rows 321 7 164 26 112 160 64 128 256), losses := [] }

theorem u6676 : Upper (D 8) (R 8) [320,5,160,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6677 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 321 7 164 41 50 40 208 208 464), lower := (rows 321 7 164 41 50 40 64 128 256), losses := [] }

theorem u6677 : Upper (D 8) (R 8) [320,5,160,33,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6677 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6678 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 321 7 164 41 50 48 200 200 456), lower := (rows 321 7 164 41 50 48 64 128 256), losses := [] }

theorem u6678 : Upper (D 8) (R 8) [320,5,160,33,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6678 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6679 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 150, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 164 41 50 96 216 152 408), lower := (rows 321 7 164 41 50 96 64 128 256), losses := [] }

theorem u6679 : Upper (D 8) (R 8) [320,5,160,33,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6680 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 41 50 160 88 216 344), lower := (rows 321 7 164 41 50 160 64 128 256), losses := [] }

theorem u6680 : Upper (D 8) (R 8) [320,5,160,33,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6681 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 321 7 164 41 82 40 240 176 432), lower := (rows 321 7 164 41 82 40 64 128 256), losses := [] }

theorem u6681 : Upper (D 8) (R 8) [320,5,160,33,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6681 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6682 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 321 7 164 41 82 48 232 168 424), lower := (rows 321 7 164 41 82 48 64 128 256), losses := [] }

theorem u6682 : Upper (D 8) (R 8) [320,5,160,33,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6682 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6683 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 41 82 160 120 184 312), lower := (rows 321 7 164 41 82 160 64 128 256), losses := [] }

theorem u6683 : Upper (D 8) (R 8) [320,5,160,33,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6684 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 321 7 164 41 88 34 240 176 432), lower := (rows 321 7 164 41 88 34 64 128 256), losses := [] }

theorem u6684 : Upper (D 8) (R 8) [320,5,160,33,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6684 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6685 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 321 7 164 41 88 48 226 162 418), lower := (rows 321 7 164 41 88 48 64 128 256), losses := [] }

theorem u6685 : Upper (D 8) (R 8) [320,5,160,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6685 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6686 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 41 88 160 114 178 306), lower := (rows 321 7 164 41 88 160 64 128 256), losses := [] }

theorem u6686 : Upper (D 8) (R 8) [320,5,160,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6687 : PairBound 9 := { available := 152, camps := [], pairs := [], upper := (rows 321 7 164 41 112 34 216 152 408), lower := (rows 321 7 164 41 112 34 64 128 256), losses := [] }

theorem u6687 : Upper (D 8) (R 8) [320,5,160,33,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6687 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6688 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 321 7 164 41 112 40 210 146 402), lower := (rows 321 7 164 41 112 40 64 128 256), losses := [] }

theorem u6688 : Upper (D 8) (R 8) [320,5,160,33,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6688 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6689 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 321 7 164 41 112 48 202 138 394), lower := (rows 321 7 164 41 112 48 64 128 256), losses := [] }

theorem u6689 : Upper (D 8) (R 8) [320,5,160,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6689 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6690 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 41 112 160 90 154 282), lower := (rows 321 7 164 41 112 160 64 128 256), losses := [] }

theorem u6690 : Upper (D 8) (R 8) [320,5,160,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6691 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 321 7 164 41 152 34 112 240 368), lower := (rows 321 7 164 41 152 34 64 128 256), losses := [] }

theorem u6691 : Upper (D 8) (R 8) [320,5,160,33,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6691 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6692 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 321 7 164 41 152 48 98 226 354), lower := (rows 321 7 164 41 152 48 64 128 256), losses := [] }

theorem u6692 : Upper (D 8) (R 8) [320,5,160,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6692 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6693 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 150, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 164 41 152 96 114 178 306), lower := (rows 321 7 164 41 152 96 64 128 256), losses := [] }

theorem u6693 : Upper (D 8) (R 8) [320,5,160,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6694 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 321 7 164 41 208 34 120 184 312), lower := (rows 321 7 164 41 208 34 64 128 256), losses := [] }

theorem u6694 : Upper (D 8) (R 8) [320,5,160,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6694 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6695 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 321 7 164 41 208 40 114 178 306), lower := (rows 321 7 164 41 208 40 64 128 256), losses := [] }

theorem u6695 : Upper (D 8) (R 8) [320,5,160,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6695 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6696 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 321 7 164 41 208 48 106 170 298), lower := (rows 321 7 164 41 208 48 64 128 256), losses := [] }

theorem u6696 : Upper (D 8) (R 8) [320,5,160,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6696 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6697 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 164 42 88 33 240 176 432), lower := (rows 321 7 164 42 88 33 64 128 256), losses := [] }

theorem u6697 : Upper (D 8) (R 8) [320,5,160,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6698 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 7 164 42 88 48 225 161 417), lower := (rows 321 7 164 42 88 48 64 128 256), losses := [] }

theorem u6698 : Upper (D 8) (R 8) [320,5,160,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6698 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6699 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 42 88 160 113 177 305), lower := (rows 321 7 164 42 88 160 64 128 256), losses := [] }

theorem u6699 : Upper (D 8) (R 8) [320,5,160,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6700 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 164 42 112 33 216 152 408), lower := (rows 321 7 164 42 112 33 64 128 256), losses := [] }

theorem u6700 : Upper (D 8) (R 8) [320,5,160,34,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6701 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 321 7 164 42 112 40 209 145 401), lower := (rows 321 7 164 42 112 40 64 128 256), losses := [] }

theorem u6701 : Upper (D 8) (R 8) [320,5,160,34,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6701 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6702 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 321 7 164 42 112 48 201 137 393), lower := (rows 321 7 164 42 112 48 64 128 256), losses := [] }

theorem u6702 : Upper (D 8) (R 8) [320,5,160,34,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6702 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6703 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 42 112 160 89 153 281), lower := (rows 321 7 164 42 112 160 64 128 256), losses := [] }

theorem u6703 : Upper (D 8) (R 8) [320,5,160,34,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6704 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 321 7 164 42 145 40 112 240 368), lower := (rows 321 7 164 42 145 40 64 128 256), losses := [] }

theorem u6704 : Upper (D 8) (R 8) [320,5,160,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6704 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6705 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 321 7 164 42 145 48 104 232 360), lower := (rows 321 7 164 42 145 48 64 128 256), losses := [] }

theorem u6705 : Upper (D 8) (R 8) [320,5,160,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6705 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6706 : PairBound 9 := { available := 56, camps := [], pairs := [(2,0)], upper := (rows 321 7 164 42 145 96 120 184 312), lower := (rows 321 7 164 42 145 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 10 16 97 64 128 256), good := (rows 352 46 164 42 180 96 96 128 256) }] }

theorem u6706 : Upper (D 8) (R 8) [320,5,160,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6707 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 164 42 208 33 120 184 312), lower := (rows 321 7 164 42 208 33 64 128 256), losses := [] }

theorem u6707 : Upper (D 8) (R 8) [320,5,160,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6708 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 7 164 42 208 40 113 177 305), lower := (rows 321 7 164 42 208 40 64 128 256), losses := [] }

theorem u6708 : Upper (D 8) (R 8) [320,5,160,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6708 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6709 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 321 7 164 42 208 48 105 169 297), lower := (rows 321 7 164 42 208 48 64 128 256), losses := [] }

theorem u6709 : Upper (D 8) (R 8) [320,5,160,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6709 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6710 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 164 56 82 33 232 168 424), lower := (rows 321 7 164 56 82 33 64 128 256), losses := [] }

theorem u6710 : Upper (D 8) (R 8) [320,5,160,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6711 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 7 164 56 82 40 225 161 417), lower := (rows 321 7 164 56 82 40 64 128 256), losses := [] }

theorem u6711 : Upper (D 8) (R 8) [320,5,160,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6711 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6712 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 56 82 160 105 169 297), lower := (rows 321 7 164 56 82 160 64 128 256), losses := [] }

theorem u6712 : Upper (D 8) (R 8) [320,5,160,48,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6713 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 321 7 164 56 145 34 104 232 360), lower := (rows 321 7 164 56 145 34 64 128 256), losses := [] }

theorem u6713 : Upper (D 8) (R 8) [320,5,160,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6713 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6714 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 321 7 164 56 145 40 98 226 354), lower := (rows 321 7 164 56 145 40 64 128 256), losses := [] }

theorem u6714 : Upper (D 8) (R 8) [320,5,160,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6714 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6715 : PairBound 9 := { available := 42, camps := [], pairs := [(2,0)], upper := (rows 321 7 164 56 145 96 106 170 298), lower := (rows 321 7 164 56 145 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 97 64 128 256), good := (rows 352 38 164 60 188 96 96 128 256) }] }

theorem u6715 : Upper (D 8) (R 8) [320,5,160,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6716 : Route 9 := (fun mask => (mask,id))

def c6716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6716 : Upper (D 8) (R 8) [320,5,160,48,192,1] 13 := by
  apply FastRouting.sound _ _ [320,5,160,48,192,1] 13 (by decide) (choices 1) [2,8,32] r6716 c6716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u845
  · exact u846
  · exact u847

def b6717 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 321 7 164 56 208 34 105 169 297), lower := (rows 321 7 164 56 208 34 64 128 256), losses := [] }

theorem u6717 : Upper (D 8) (R 8) [320,5,160,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6717 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6718 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 321 7 164 56 208 40 99 163 291), lower := (rows 321 7 164 56 208 40 64 128 256), losses := [] }

theorem u6718 : Upper (D 8) (R 8) [320,5,160,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6718 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6719 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 321 7 164 74 145 40 112 176 304), lower := (rows 321 7 164 74 145 40 64 128 256), losses := [] }

theorem u6719 : Upper (D 8) (R 8) [320,5,160,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6719 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6719
end Delivery.IrregularNine14.P08
