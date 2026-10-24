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

def b5760 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 261 104 176 33 90 154 282), lower := (rows 193 38 261 104 176 33 64 128 256), losses := [] }

theorem u5760 : Upper (D 8) (R 8) [192,36,257,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5761 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 193 38 261 104 176 34 89 153 281), lower := (rows 193 38 261 104 176 34 64 128 256), losses := [] }

theorem u5761 : Upper (D 8) (R 8) [192,36,257,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5761 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5762 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 193 38 261 104 176 40 83 147 275), lower := (rows 193 38 261 104 176 40 64 128 256), losses := [] }

theorem u5762 : Upper (D 8) (R 8) [192,36,257,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5762 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5763 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 262 88 176 33 105 169 297), lower := (rows 193 38 262 88 176 33 64 128 256), losses := [] }

theorem u5763 : Upper (D 8) (R 8) [192,36,258,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5764 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 262 88 176 40 97 161 289), lower := (rows 193 38 262 88 176 40 64 128 256), losses := [] }

theorem u5764 : Upper (D 8) (R 8) [192,36,258,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5764 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5765 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 262 104 176 33 89 153 281), lower := (rows 193 38 262 104 176 33 64 128 256), losses := [] }

theorem u5765 : Upper (D 8) (R 8) [192,36,258,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5766 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 193 38 262 104 176 40 81 145 273), lower := (rows 193 38 262 104 176 40 64 128 256), losses := [] }

theorem u5766 : Upper (D 8) (R 8) [192,36,258,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5766 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5767 : PairBound 9 := { available := 33, camps := [], pairs := [(4,6)], upper := (rows 193 38 268 88 146 33 97 161 289), lower := (rows 193 38 268 88 146 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 18 33 0 161 289), good := (rows 417 438 268 24 146 417 0 128 256) }] }

theorem u5767 : Upper (D 8) (R 8) [192,36,264,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5768 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 268 88 176 33 99 163 291), lower := (rows 193 38 268 88 176 33 64 128 256), losses := [] }

theorem u5768 : Upper (D 8) (R 8) [192,36,264,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5769 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 268 88 176 34 97 161 289), lower := (rows 193 38 268 88 176 34 64 128 256), losses := [] }

theorem u5769 : Upper (D 8) (R 8) [192,36,264,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5769 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5770 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 193 38 268 104 146 33 113 177 305), lower := (rows 193 38 268 104 146 33 64 128 256), losses := [] }

theorem u5770 : Upper (D 8) (R 8) [192,36,264,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5771 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 268 104 146 48 97 161 289), lower := (rows 193 38 268 104 146 48 64 128 256), losses := [] }

theorem u5771 : Upper (D 8) (R 8) [192,36,264,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5771 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5772 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 268 104 176 33 83 147 275), lower := (rows 193 38 268 104 176 33 64 128 256), losses := [] }

theorem u5772 : Upper (D 8) (R 8) [192,36,264,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5773 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 193 38 268 104 176 34 81 145 273), lower := (rows 193 38 268 104 176 34 64 128 256), losses := [] }

theorem u5773 : Upper (D 8) (R 8) [192,36,264,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5773 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5774 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 193 38 268 104 176 48 67 131 259), lower := (rows 193 38 268 104 176 48 64 128 256), losses := [] }

theorem u5774 : Upper (D 8) (R 8) [192,36,264,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5774 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5775 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 28 104 176 33 224 224 480), lower := (rows 259 7 28 104 176 33 64 128 256), losses := [] }

theorem u5775 : Upper (D 8) (R 8) [258,5,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5776 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 28 104 176 96 225 161 417), lower := (rows 259 7 28 104 176 96 64 128 256), losses := [] }

theorem u5776 : Upper (D 8) (R 8) [258,5,24,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5777 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 88 176 33 224 224 480), lower := (rows 259 7 44 88 176 33 64 128 256), losses := [] }

theorem u5777 : Upper (D 8) (R 8) [258,5,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5778 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 44 88 176 96 225 161 417), lower := (rows 259 7 44 88 176 96 64 128 256), losses := [] }

theorem u5778 : Upper (D 8) (R 8) [258,5,40,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5779 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 44 88 176 160 97 225 353), lower := (rows 259 7 44 88 176 160 64 128 256), losses := [] }

theorem u5779 : Upper (D 8) (R 8) [258,5,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5780 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 200 112 33 240 176 432), lower := (rows 259 7 44 200 112 33 64 128 256), losses := [] }

theorem u5780 : Upper (D 8) (R 8) [258,5,40,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5781 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 7 44 200 112 48 225 161 417), lower := (rows 259 7 44 200 112 48 64 128 256), losses := [] }

theorem u5781 : Upper (D 8) (R 8) [258,5,40,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5781 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5782 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 44 200 112 160 113 177 305), lower := (rows 259 7 44 200 112 160 64 128 256), losses := [] }

theorem u5782 : Upper (D 8) (R 8) [258,5,40,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5783 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 168 112 33 240 176 432), lower := (rows 259 7 76 168 112 33 64 128 256), losses := [] }

theorem u5783 : Upper (D 8) (R 8) [258,5,72,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5784 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 7 76 168 112 48 225 161 417), lower := (rows 259 7 76 168 112 48 64 128 256), losses := [] }

theorem u5784 : Upper (D 8) (R 8) [258,5,72,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5784 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5785 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 76 168 112 160 113 177 305), lower := (rows 259 7 76 168 112 160 64 128 256), losses := [] }

theorem u5785 : Upper (D 8) (R 8) [258,5,72,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5786 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 168 208 33 112 176 304), lower := (rows 259 7 76 168 208 33 64 128 256), losses := [] }

theorem u5786 : Upper (D 8) (R 8) [258,5,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5787 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 7 76 168 208 48 97 161 289), lower := (rows 259 7 76 168 208 48 64 128 256), losses := [] }

theorem u5787 : Upper (D 8) (R 8) [258,5,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5787 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5788 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 56 152 33 224 224 480), lower := (rows 259 7 100 56 152 33 64 128 256), losses := [] }

theorem u5788 : Upper (D 8) (R 8) [258,5,96,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5789 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 100 56 152 96 225 161 417), lower := (rows 259 7 100 56 152 96 64 128 256), losses := [] }

theorem u5789 : Upper (D 8) (R 8) [258,5,96,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5790 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 56 152 160 97 225 353), lower := (rows 259 7 100 56 152 160 64 128 256), losses := [] }

theorem u5790 : Upper (D 8) (R 8) [258,5,96,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5791 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 56 208 33 232 168 424), lower := (rows 259 7 100 56 208 33 64 128 256), losses := [] }

theorem u5791 : Upper (D 8) (R 8) [258,5,96,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5792 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 7 100 56 208 40 225 161 417), lower := (rows 259 7 100 56 208 40 64 128 256), losses := [] }

theorem u5792 : Upper (D 8) (R 8) [258,5,96,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5792 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5793 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 56 208 160 105 169 297), lower := (rows 259 7 100 56 208 160 64 128 256), losses := [] }

theorem u5793 : Upper (D 8) (R 8) [258,5,96,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5794 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 88 176 33 232 168 424), lower := (rows 259 7 100 88 176 33 64 128 256), losses := [] }

theorem u5794 : Upper (D 8) (R 8) [258,5,96,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5795 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 7 100 88 176 40 225 161 417), lower := (rows 259 7 100 88 176 40 64 128 256), losses := [] }

theorem u5795 : Upper (D 8) (R 8) [258,5,96,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5795 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5796 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 88 176 160 105 169 297), lower := (rows 259 7 100 88 176 160 64 128 256), losses := [] }

theorem u5796 : Upper (D 8) (R 8) [258,5,96,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5797 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 168 208 33 120 184 312), lower := (rows 259 7 100 168 208 33 64 128 256), losses := [] }

theorem u5797 : Upper (D 8) (R 8) [258,5,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5798 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 7 100 168 208 40 113 177 305), lower := (rows 259 7 100 168 208 40 64 128 256), losses := [] }

theorem u5798 : Upper (D 8) (R 8) [258,5,96,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5798 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5799 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 259 7 100 168 208 48 105 169 297), lower := (rows 259 7 100 168 208 48 64 128 256), losses := [] }

theorem u5799 : Upper (D 8) (R 8) [258,5,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5799 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5800 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 88 176 33 104 168 296), lower := (rows 259 7 196 88 176 33 64 128 256), losses := [] }

theorem u5800 : Upper (D 8) (R 8) [258,5,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5801 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 7 196 88 176 40 97 161 289), lower := (rows 259 7 196 88 176 40 64 128 256), losses := [] }

theorem u5801 : Upper (D 8) (R 8) [258,5,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5801 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5802 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 104 176 33 120 184 312), lower := (rows 259 7 196 104 176 33 64 128 256), losses := [] }

theorem u5802 : Upper (D 8) (R 8) [258,5,192,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5803 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 7 196 104 176 40 113 177 305), lower := (rows 259 7 196 104 176 40 64 128 256), losses := [] }

theorem u5803 : Upper (D 8) (R 8) [258,5,192,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5803 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5804 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 21 104 176 33 224 224 480), lower := (rows 259 14 21 104 176 33 64 128 256), losses := [] }

theorem u5804 : Upper (D 8) (R 8) [258,12,17,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5805 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 21 104 176 96 225 161 417), lower := (rows 259 14 21 104 176 96 64 128 256), losses := [] }

theorem u5805 : Upper (D 8) (R 8) [258,12,17,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5806 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 21 104 176 160 97 225 353), lower := (rows 259 14 21 104 176 160 64 128 256), losses := [] }

theorem u5806 : Upper (D 8) (R 8) [258,12,17,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5807 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 37 56 208 33 224 224 480), lower := (rows 259 14 37 56 208 33 64 128 256), losses := [] }

theorem u5807 : Upper (D 8) (R 8) [258,12,33,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5808 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 37 56 208 96 225 161 417), lower := (rows 259 14 37 56 208 96 64 128 256), losses := [] }

theorem u5808 : Upper (D 8) (R 8) [258,12,33,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5809 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 37 88 176 33 224 224 480), lower := (rows 259 14 37 88 176 33 64 128 256), losses := [] }

theorem u5809 : Upper (D 8) (R 8) [258,12,33,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5810 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 259 14 37 88 176 96 225 161 417), lower := (rows 259 14 37 88 176 96 64 128 256), losses := [] }

theorem u5810 : Upper (D 8) (R 8) [258,12,33,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5811 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 37 88 176 160 97 225 353), lower := (rows 259 14 37 88 176 160 64 128 256), losses := [] }

theorem u5811 : Upper (D 8) (R 8) [258,12,33,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5812 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 37 104 176 33 208 208 464), lower := (rows 259 14 37 104 176 33 64 128 256), losses := [] }

theorem u5812 : Upper (D 8) (R 8) [258,12,33,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5813 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 14 37 104 176 48 193 193 449), lower := (rows 259 14 37 104 176 48 64 128 256), losses := [] }

theorem u5813 : Upper (D 8) (R 8) [258,12,33,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5813 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5814 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 37 104 176 96 209 145 401), lower := (rows 259 14 37 104 176 96 64 128 256), losses := [] }

theorem u5814 : Upper (D 8) (R 8) [258,12,33,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5815 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 37 104 176 160 81 209 337), lower := (rows 259 14 37 104 176 160 64 128 256), losses := [] }

theorem u5815 : Upper (D 8) (R 8) [258,12,33,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5816 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 37 104 208 33 240 176 432), lower := (rows 259 14 37 104 208 33 64 128 256), losses := [] }

theorem u5816 : Upper (D 8) (R 8) [258,12,33,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5817 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 14 37 104 208 48 225 161 417), lower := (rows 259 14 37 104 208 48 64 128 256), losses := [] }

theorem u5817 : Upper (D 8) (R 8) [258,12,33,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5817 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5818 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 259 14 37 104 208 160 113 177 305), lower := (rows 259 14 37 104 208 160 64 128 256), losses := [] }

theorem u5818 : Upper (D 8) (R 8) [258,12,33,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5819 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 37 200 112 33 240 176 432), lower := (rows 259 14 37 200 112 33 64 128 256), losses := [] }

theorem u5819 : Upper (D 8) (R 8) [258,12,33,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5819
end Delivery.IrregularNine14.P08
