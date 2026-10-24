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

def b4800 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 328 50 160 97 161 289), lower := (rows 97 14 148 328 50 160 64 128 256), losses := [] }

theorem u4800 : Upper (D 8) (R 8) [96,12,144,320,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4801 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 164 265 50 33 208 208 464), lower := (rows 97 14 164 265 50 33 64 128 256), losses := [] }

theorem u4801 : Upper (D 8) (R 8) [96,12,160,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4802 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 14 164 265 50 48 193 193 449), lower := (rows 97 14 164 265 50 48 64 128 256), losses := [] }

theorem u4802 : Upper (D 8) (R 8) [96,12,160,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4802 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4803 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 164 265 50 96 209 145 401), lower := (rows 97 14 164 265 50 96 64 128 256), losses := [] }

theorem u4803 : Upper (D 8) (R 8) [96,12,160,257,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4804 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 265 50 160 81 209 337), lower := (rows 97 14 164 265 50 160 64 128 256), losses := [] }

theorem u4804 : Upper (D 8) (R 8) [96,12,160,257,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4805 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 265 82 33 240 176 432), lower := (rows 97 14 164 265 82 33 64 128 256), losses := [] }

theorem u4805 : Upper (D 8) (R 8) [96,12,160,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4806 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 164 265 82 48 225 161 417), lower := (rows 97 14 164 265 82 48 64 128 256), losses := [] }

theorem u4806 : Upper (D 8) (R 8) [96,12,160,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4806 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4807 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 265 82 160 113 177 305), lower := (rows 97 14 164 265 82 160 64 128 256), losses := [] }

theorem u4807 : Upper (D 8) (R 8) [96,12,160,257,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4808 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 97 14 164 265 145 34 112 240 368), lower := (rows 97 14 164 265 145 34 64 128 256), losses := [] }

theorem u4808 : Upper (D 8) (R 8) [96,12,160,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4808 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4809 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 97 14 164 265 145 48 98 226 354), lower := (rows 97 14 164 265 145 48 64 128 256), losses := [] }

theorem u4809 : Upper (D 8) (R 8) [96,12,160,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4809 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4810 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 164 265 145 96 114 178 306), lower := (rows 97 14 164 265 145 96 64 128 256), losses := [] }

theorem u4810 : Upper (D 8) (R 8) [96,12,160,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4811 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 265 208 33 114 178 306), lower := (rows 97 14 164 265 208 33 64 128 256), losses := [] }

theorem u4811 : Upper (D 8) (R 8) [96,12,160,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4812 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 14 164 265 208 34 113 177 305), lower := (rows 97 14 164 265 208 34 64 128 256), losses := [] }

theorem u4812 : Upper (D 8) (R 8) [96,12,160,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4812 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4813 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 14 164 265 208 48 99 163 291), lower := (rows 97 14 164 265 208 48 64 128 256), losses := [] }

theorem u4813 : Upper (D 8) (R 8) [96,12,160,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4813 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4814 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 280 50 33 193 193 449), lower := (rows 97 14 164 280 50 33 64 128 256), losses := [] }

theorem u4814 : Upper (D 8) (R 8) [96,12,160,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4815 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 164 280 50 96 193 129 385), lower := (rows 97 14 164 280 50 96 64 128 256), losses := [] }

theorem u4815 : Upper (D 8) (R 8) [96,12,160,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4816 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 280 50 160 65 193 321), lower := (rows 97 14 164 280 50 160 64 128 256), losses := [] }

theorem u4816 : Upper (D 8) (R 8) [96,12,160,272,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4817 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 296 82 33 209 145 401), lower := (rows 97 14 164 296 82 33 64 128 256), losses := [] }

theorem u4817 : Upper (D 8) (R 8) [96,12,160,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4818 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 164 296 82 48 193 129 385), lower := (rows 97 14 164 296 82 48 64 128 256), losses := [] }

theorem u4818 : Upper (D 8) (R 8) [96,12,160,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4818 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4819 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 296 82 160 81 145 273), lower := (rows 97 14 164 296 82 160 64 128 256), losses := [] }

theorem u4819 : Upper (D 8) (R 8) [96,12,160,288,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4820 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 164 296 145 33 82 210 338), lower := (rows 97 14 164 296 145 33 64 128 256), losses := [] }

theorem u4820 : Upper (D 8) (R 8) [96,12,160,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4821 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 14 164 296 145 34 81 209 337), lower := (rows 97 14 164 296 145 34 64 128 256), losses := [] }

theorem u4821 : Upper (D 8) (R 8) [96,12,160,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4821 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4822 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 14 164 296 145 48 67 195 323), lower := (rows 97 14 164 296 145 48 64 128 256), losses := [] }

theorem u4822 : Upper (D 8) (R 8) [96,12,160,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4822 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4823 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 164 296 145 96 83 147 275), lower := (rows 97 14 164 296 145 96 64 128 256), losses := [] }

theorem u4823 : Upper (D 8) (R 8) [96,12,160,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4824 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 296 208 33 83 147 275), lower := (rows 97 14 164 296 208 33 64 128 256), losses := [] }

theorem u4824 : Upper (D 8) (R 8) [96,12,160,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4825 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 14 164 296 208 34 81 145 273), lower := (rows 97 14 164 296 208 34 64 128 256), losses := [] }

theorem u4825 : Upper (D 8) (R 8) [96,12,160,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4825 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4826 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 14 164 296 208 48 67 131 259), lower := (rows 97 14 164 296 208 48 64 128 256), losses := [] }

theorem u4826 : Upper (D 8) (R 8) [96,12,160,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4826 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4827 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 328 50 33 209 145 401), lower := (rows 97 14 164 328 50 33 64 128 256), losses := [] }

theorem u4827 : Upper (D 8) (R 8) [96,12,160,320,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4828 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 164 328 50 48 193 129 385), lower := (rows 97 14 164 328 50 48 64 128 256), losses := [] }

theorem u4828 : Upper (D 8) (R 8) [96,12,160,320,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4828 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4829 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 328 50 160 81 145 273), lower := (rows 97 14 164 328 50 160 64 128 256), losses := [] }

theorem u4829 : Upper (D 8) (R 8) [96,12,160,320,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4830 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 328 145 33 114 178 306), lower := (rows 97 14 164 328 145 33 64 128 256), losses := [] }

theorem u4830 : Upper (D 8) (R 8) [96,12,160,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4831 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 14 164 328 145 34 113 177 305), lower := (rows 97 14 164 328 145 34 64 128 256), losses := [] }

theorem u4831 : Upper (D 8) (R 8) [96,12,160,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4831 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4832 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 14 164 328 145 48 99 163 291), lower := (rows 97 14 164 328 145 48 64 128 256), losses := [] }

theorem u4832 : Upper (D 8) (R 8) [96,12,160,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4832 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4833 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 265 50 33 240 176 432), lower := (rows 97 14 196 265 50 33 64 128 256), losses := [] }

theorem u4833 : Upper (D 8) (R 8) [96,12,192,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4834 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 14 196 265 50 48 225 161 417), lower := (rows 97 14 196 265 50 48 64 128 256), losses := [] }

theorem u4834 : Upper (D 8) (R 8) [96,12,192,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4834 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4835 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 265 50 160 113 177 305), lower := (rows 97 14 196 265 50 160 64 128 256), losses := [] }

theorem u4835 : Upper (D 8) (R 8) [96,12,192,257,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4836 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 97 14 196 265 145 34 112 176 304), lower := (rows 97 14 196 265 145 34 64 128 256), losses := [] }

theorem u4836 : Upper (D 8) (R 8) [96,12,192,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4836 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4837 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 97 14 196 265 145 48 98 162 290), lower := (rows 97 14 196 265 145 48 64 128 256), losses := [] }

theorem u4837 : Upper (D 8) (R 8) [96,12,192,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4837 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4838 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 265 176 33 114 178 306), lower := (rows 97 14 196 265 176 33 64 128 256), losses := [] }

theorem u4838 : Upper (D 8) (R 8) [96,12,192,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4839 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 14 196 265 176 34 113 177 305), lower := (rows 97 14 196 265 176 34 64 128 256), losses := [] }

theorem u4839 : Upper (D 8) (R 8) [96,12,192,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4839 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4840 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 14 196 265 176 48 99 163 291), lower := (rows 97 14 196 265 176 48 64 128 256), losses := [] }

theorem u4840 : Upper (D 8) (R 8) [96,12,192,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4840 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4841 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 280 50 33 225 161 417), lower := (rows 97 14 196 280 50 33 64 128 256), losses := [] }

theorem u4841 : Upper (D 8) (R 8) [96,12,192,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4842 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 280 50 160 97 161 289), lower := (rows 97 14 196 280 50 160 64 128 256), losses := [] }

theorem u4842 : Upper (D 8) (R 8) [96,12,192,272,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4843 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 296 50 33 209 145 401), lower := (rows 97 14 196 296 50 33 64 128 256), losses := [] }

theorem u4843 : Upper (D 8) (R 8) [96,12,192,288,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4844 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 196 296 50 48 193 129 385), lower := (rows 97 14 196 296 50 48 64 128 256), losses := [] }

theorem u4844 : Upper (D 8) (R 8) [96,12,192,288,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4844 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4845 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 296 50 160 81 145 273), lower := (rows 97 14 196 296 50 160 64 128 256), losses := [] }

theorem u4845 : Upper (D 8) (R 8) [96,12,192,288,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4846 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 296 145 33 114 178 306), lower := (rows 97 14 196 296 145 33 64 128 256), losses := [] }

theorem u4846 : Upper (D 8) (R 8) [96,12,192,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4847 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 14 196 296 145 34 113 177 305), lower := (rows 97 14 196 296 145 34 64 128 256), losses := [] }

theorem u4847 : Upper (D 8) (R 8) [96,12,192,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4847 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4848 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 14 196 296 145 48 99 163 291), lower := (rows 97 14 196 296 145 48 64 128 256), losses := [] }

theorem u4848 : Upper (D 8) (R 8) [96,12,192,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4848 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4849 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 196 296 176 33 83 147 275), lower := (rows 97 14 196 296 176 33 64 128 256), losses := [] }

theorem u4849 : Upper (D 8) (R 8) [96,12,192,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4850 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 14 196 296 176 34 81 145 273), lower := (rows 97 14 196 296 176 34 64 128 256), losses := [] }

theorem u4850 : Upper (D 8) (R 8) [96,12,192,288,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4850 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4851 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 14 196 296 176 48 67 131 259), lower := (rows 97 14 196 296 176 48 64 128 256), losses := [] }

theorem u4851 : Upper (D 8) (R 8) [96,12,192,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4851 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4852 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 56 145 33 450 386 386), lower := (rows 97 38 76 56 145 33 64 128 256), losses := [] }

theorem u4852 : Upper (D 8) (R 8) [96,36,72,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4853 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 97 38 76 56 145 34 449 385 385), lower := (rows 97 38 76 56 145 34 64 128 256), losses := [] }

theorem u4853 : Upper (D 8) (R 8) [96,36,72,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4853 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4854 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 56 145 160 323 387 259), lower := (rows 97 38 76 56 145 160 64 128 256), losses := [] }

theorem u4854 : Upper (D 8) (R 8) [96,36,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4855 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 76 56 145 288 195 131 387), lower := (rows 97 38 76 56 145 288 64 128 256), losses := [] }

theorem u4855 : Upper (D 8) (R 8) [96,36,72,48,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4855 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4856 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 56 146 33 449 385 385), lower := (rows 97 38 76 56 146 33 64 128 256), losses := [] }

theorem u4856 : Upper (D 8) (R 8) [96,36,72,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4857 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 56 146 160 321 385 257), lower := (rows 97 38 76 56 146 160 64 128 256), losses := [] }

theorem u4857 : Upper (D 8) (R 8) [96,36,72,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4858 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 56 146 288 193 129 385), lower := (rows 97 38 76 56 146 288 64 128 256), losses := [] }

theorem u4858 : Upper (D 8) (R 8) [96,36,72,48,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4858 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4859 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 56 273 33 194 130 386), lower := (rows 97 38 76 56 273 33 64 128 256), losses := [] }

theorem u4859 : Upper (D 8) (R 8) [96,36,72,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4859
end Delivery.IrregularNine14.P08
