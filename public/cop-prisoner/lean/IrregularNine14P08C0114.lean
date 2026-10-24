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

def b6840 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 321 35 44 88 145 34 228 164 420), lower := (rows 321 35 44 88 145 34 64 128 256), losses := [] }

theorem u6840 : Upper (D 8) (R 8) [320,33,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6840 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6841 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 321 35 44 88 145 36 226 162 418), lower := (rows 321 35 44 88 145 36 64 128 256), losses := [] }

theorem u6841 : Upper (D 8) (R 8) [320,33,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6841 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6842 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 88 145 160 102 166 294), lower := (rows 321 35 44 88 145 160 64 128 256), losses := [] }

theorem u6842 : Upper (D 8) (R 8) [320,33,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6843 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 88 146 33 228 164 420), lower := (rows 321 35 44 88 146 33 64 128 256), losses := [] }

theorem u6843 : Upper (D 8) (R 8) [320,33,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6844 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 35 44 88 146 36 225 161 417), lower := (rows 321 35 44 88 146 36 64 128 256), losses := [] }

theorem u6844 : Upper (D 8) (R 8) [320,33,40,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6844 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6845 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 88 146 160 101 165 293), lower := (rows 321 35 44 88 146 160 64 128 256), losses := [] }

theorem u6845 : Upper (D 8) (R 8) [320,33,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6846 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 88 176 33 198 134 390), lower := (rows 321 35 44 88 176 33 64 128 256), losses := [] }

theorem u6846 : Upper (D 8) (R 8) [320,33,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6847 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 321 35 44 88 176 34 197 133 389), lower := (rows 321 35 44 88 176 34 64 128 256), losses := [] }

theorem u6847 : Upper (D 8) (R 8) [320,33,40,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6847 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6848 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 321 35 44 88 176 36 195 131 387), lower := (rows 321 35 44 88 176 36 64 128 256), losses := [] }

theorem u6848 : Upper (D 8) (R 8) [320,33,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6848 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6849 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 88 176 160 71 135 263), lower := (rows 321 35 44 88 176 160 64 128 256), losses := [] }

theorem u6849 : Upper (D 8) (R 8) [320,33,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6850 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 321 35 44 137 82 36 240 176 432), lower := (rows 321 35 44 137 82 36 64 128 256), losses := [] }

theorem u6850 : Upper (D 8) (R 8) [320,33,40,129,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6850 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6851 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 321 35 44 137 82 48 228 164 420), lower := (rows 321 35 44 137 82 48 64 128 256), losses := [] }

theorem u6851 : Upper (D 8) (R 8) [320,33,40,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6851 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6852 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 137 82 160 116 180 308), lower := (rows 321 35 44 137 82 160 64 128 256), losses := [] }

theorem u6852 : Upper (D 8) (R 8) [320,33,40,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6853 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 321 35 44 137 84 34 240 176 432), lower := (rows 321 35 44 137 84 34 64 128 256), losses := [] }

theorem u6853 : Upper (D 8) (R 8) [320,33,40,129,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6853 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6854 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 321 35 44 137 84 48 226 162 418), lower := (rows 321 35 44 137 84 48 64 128 256), losses := [] }

theorem u6854 : Upper (D 8) (R 8) [320,33,40,129,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6854 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6855 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 137 84 160 114 178 306), lower := (rows 321 35 44 137 84 160 64 128 256), losses := [] }

theorem u6855 : Upper (D 8) (R 8) [320,33,40,129,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6856 : PairBound 9 := { available := 148, camps := [], pairs := [], upper := (rows 321 35 44 137 112 34 212 148 404), lower := (rows 321 35 44 137 112 34 64 128 256), losses := [] }

theorem u6856 : Upper (D 8) (R 8) [320,33,40,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6856 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6857 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 321 35 44 137 112 36 210 146 402), lower := (rows 321 35 44 137 112 36 64 128 256), losses := [] }

theorem u6857 : Upper (D 8) (R 8) [320,33,40,129,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6857 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6858 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 321 35 44 137 112 48 198 134 390), lower := (rows 321 35 44 137 112 48 64 128 256), losses := [] }

theorem u6858 : Upper (D 8) (R 8) [320,33,40,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6858 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6859 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 137 112 160 86 150 278), lower := (rows 321 35 44 137 112 160 64 128 256), losses := [] }

theorem u6859 : Upper (D 8) (R 8) [320,33,40,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6860 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 321 35 44 137 146 36 112 240 368), lower := (rows 321 35 44 137 146 36 64 128 256), losses := [] }

theorem u6860 : Upper (D 8) (R 8) [320,33,40,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6860 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6861 : PairBound 9 := { available := 100, camps := [], pairs := [], upper := (rows 321 35 44 137 146 48 100 228 356), lower := (rows 321 35 44 137 146 48 64 128 256), losses := [] }

theorem u6861 : Upper (D 8) (R 8) [320,33,40,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6861 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6862 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 44 137 146 96 116 180 308), lower := (rows 321 35 44 137 146 96 64 128 256), losses := [] }

theorem u6862 : Upper (D 8) (R 8) [320,33,40,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6863 : PairBound 9 := { available := 84, camps := [], pairs := [], upper := (rows 321 35 44 137 176 34 84 212 340), lower := (rows 321 35 44 137 176 34 64 128 256), losses := [] }

theorem u6863 : Upper (D 8) (R 8) [320,33,40,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6863 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6864 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 321 35 44 137 176 36 82 210 338), lower := (rows 321 35 44 137 176 36 64 128 256), losses := [] }

theorem u6864 : Upper (D 8) (R 8) [320,33,40,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6864 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6865 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 321 35 44 137 176 48 70 198 326), lower := (rows 321 35 44 137 176 48 64 128 256), losses := [] }

theorem u6865 : Upper (D 8) (R 8) [320,33,40,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6865 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6866 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 44 137 176 96 86 150 278), lower := (rows 321 35 44 137 176 96 64 128 256), losses := [] }

theorem u6866 : Upper (D 8) (R 8) [320,33,40,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6867 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 321 35 44 137 208 34 116 180 308), lower := (rows 321 35 44 137 208 34 64 128 256), losses := [] }

theorem u6867 : Upper (D 8) (R 8) [320,33,40,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6867 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6868 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 321 35 44 137 208 36 114 178 306), lower := (rows 321 35 44 137 208 36 64 128 256), losses := [] }

theorem u6868 : Upper (D 8) (R 8) [320,33,40,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6868 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6869 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 321 35 44 137 208 48 102 166 294), lower := (rows 321 35 44 137 208 48 64 128 256), losses := [] }

theorem u6869 : Upper (D 8) (R 8) [320,33,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6869 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6870 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 138 84 33 240 176 432), lower := (rows 321 35 44 138 84 33 64 128 256), losses := [] }

theorem u6870 : Upper (D 8) (R 8) [320,33,40,130,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6871 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 35 44 138 84 48 225 161 417), lower := (rows 321 35 44 138 84 48 64 128 256), losses := [] }

theorem u6871 : Upper (D 8) (R 8) [320,33,40,130,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6871 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6872 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 138 84 160 113 177 305), lower := (rows 321 35 44 138 84 160 64 128 256), losses := [] }

theorem u6872 : Upper (D 8) (R 8) [320,33,40,130,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6873 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 138 112 33 212 148 404), lower := (rows 321 35 44 138 112 33 64 128 256), losses := [] }

theorem u6873 : Upper (D 8) (R 8) [320,33,40,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6874 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 321 35 44 138 112 36 209 145 401), lower := (rows 321 35 44 138 112 36 64 128 256), losses := [] }

theorem u6874 : Upper (D 8) (R 8) [320,33,40,130,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6874 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6875 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 321 35 44 138 112 48 197 133 389), lower := (rows 321 35 44 138 112 48 64 128 256), losses := [] }

theorem u6875 : Upper (D 8) (R 8) [320,33,40,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6875 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6876 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 138 112 160 85 149 277), lower := (rows 321 35 44 138 112 160 64 128 256), losses := [] }

theorem u6876 : Upper (D 8) (R 8) [320,33,40,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6877 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 321 35 44 138 145 36 112 240 368), lower := (rows 321 35 44 138 145 36 64 128 256), losses := [] }

theorem u6877 : Upper (D 8) (R 8) [320,33,40,130,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6877 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6878 : PairBound 9 := { available := 100, camps := [], pairs := [], upper := (rows 321 35 44 138 145 48 100 228 356), lower := (rows 321 35 44 138 145 48 64 128 256), losses := [] }

theorem u6878 : Upper (D 8) (R 8) [320,33,40,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6878 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6879 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 44 138 145 96 116 180 308), lower := (rows 321 35 44 138 145 96 64 128 256), losses := [] }

theorem u6879 : Upper (D 8) (R 8) [320,33,40,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6880 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 138 176 33 84 212 340), lower := (rows 321 35 44 138 176 33 64 128 256), losses := [] }

theorem u6880 : Upper (D 8) (R 8) [320,33,40,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6881 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 321 35 44 138 176 36 81 209 337), lower := (rows 321 35 44 138 176 36 64 128 256), losses := [] }

theorem u6881 : Upper (D 8) (R 8) [320,33,40,130,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6881 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6882 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 321 35 44 138 176 48 69 197 325), lower := (rows 321 35 44 138 176 48 64 128 256), losses := [] }

theorem u6882 : Upper (D 8) (R 8) [320,33,40,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6882 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6883 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 44 138 176 96 85 149 277), lower := (rows 321 35 44 138 176 96 64 128 256), losses := [] }

theorem u6883 : Upper (D 8) (R 8) [320,33,40,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6884 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 138 208 33 116 180 308), lower := (rows 321 35 44 138 208 33 64 128 256), losses := [] }

theorem u6884 : Upper (D 8) (R 8) [320,33,40,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6885 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 35 44 138 208 36 113 177 305), lower := (rows 321 35 44 138 208 36 64 128 256), losses := [] }

theorem u6885 : Upper (D 8) (R 8) [320,33,40,130,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6885 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6886 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 321 35 44 138 208 48 101 165 293), lower := (rows 321 35 44 138 208 48 64 128 256), losses := [] }

theorem u6886 : Upper (D 8) (R 8) [320,33,40,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6886 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6887 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 140 82 33 240 176 432), lower := (rows 321 35 44 140 82 33 64 128 256), losses := [] }

theorem u6887 : Upper (D 8) (R 8) [320,33,40,132,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6888 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 35 44 140 82 48 225 161 417), lower := (rows 321 35 44 140 82 48 64 128 256), losses := [] }

theorem u6888 : Upper (D 8) (R 8) [320,33,40,132,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6888 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6889 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 140 82 160 113 177 305), lower := (rows 321 35 44 140 82 160 64 128 256), losses := [] }

theorem u6889 : Upper (D 8) (R 8) [320,33,40,132,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6890 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 140 112 33 210 146 402), lower := (rows 321 35 44 140 112 33 64 128 256), losses := [] }

theorem u6890 : Upper (D 8) (R 8) [320,33,40,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6891 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 321 35 44 140 112 34 209 145 401), lower := (rows 321 35 44 140 112 34 64 128 256), losses := [] }

theorem u6891 : Upper (D 8) (R 8) [320,33,40,132,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6891 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6892 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 321 35 44 140 112 48 195 131 387), lower := (rows 321 35 44 140 112 48 64 128 256), losses := [] }

theorem u6892 : Upper (D 8) (R 8) [320,33,40,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6892 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6893 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 140 112 160 83 147 275), lower := (rows 321 35 44 140 112 160 64 128 256), losses := [] }

theorem u6893 : Upper (D 8) (R 8) [320,33,40,132,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6894 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 152 82 33 228 164 420), lower := (rows 321 35 44 152 82 33 64 128 256), losses := [] }

theorem u6894 : Upper (D 8) (R 8) [320,33,40,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6895 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 35 44 152 82 36 225 161 417), lower := (rows 321 35 44 152 82 36 64 128 256), losses := [] }

theorem u6895 : Upper (D 8) (R 8) [320,33,40,144,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6895 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6896 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 152 82 160 101 165 293), lower := (rows 321 35 44 152 82 160 64 128 256), losses := [] }

theorem u6896 : Upper (D 8) (R 8) [320,33,40,144,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6897 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 152 112 33 198 134 390), lower := (rows 321 35 44 152 112 33 64 128 256), losses := [] }

theorem u6897 : Upper (D 8) (R 8) [320,33,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6898 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 321 35 44 152 112 34 197 133 389), lower := (rows 321 35 44 152 112 34 64 128 256), losses := [] }

theorem u6898 : Upper (D 8) (R 8) [320,33,40,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6898 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6899 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 321 35 44 152 112 36 195 131 387), lower := (rows 321 35 44 152 112 36 64 128 256), losses := [] }

theorem u6899 : Upper (D 8) (R 8) [320,33,40,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6899 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6899
end Delivery.IrregularNine14.P08
