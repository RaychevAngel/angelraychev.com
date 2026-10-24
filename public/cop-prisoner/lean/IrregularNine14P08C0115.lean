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

def b6900 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 152 112 160 71 135 263), lower := (rows 321 35 44 152 112 160 64 128 256), losses := [] }

theorem u6900 : Upper (D 8) (R 8) [320,33,40,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6901 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 321 35 44 200 145 34 116 180 308), lower := (rows 321 35 44 200 145 34 64 128 256), losses := [] }

theorem u6901 : Upper (D 8) (R 8) [320,33,40,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6901 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6902 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 321 35 44 200 145 36 114 178 306), lower := (rows 321 35 44 200 145 36 64 128 256), losses := [] }

theorem u6902 : Upper (D 8) (R 8) [320,33,40,192,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6902 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6903 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 321 35 44 200 145 48 102 166 294), lower := (rows 321 35 44 200 145 48 64 128 256), losses := [] }

theorem u6903 : Upper (D 8) (R 8) [320,33,40,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6903 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6904 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 200 146 33 116 180 308), lower := (rows 321 35 44 200 146 33 64 128 256), losses := [] }

theorem u6904 : Upper (D 8) (R 8) [320,33,40,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6905 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 35 44 200 146 36 113 177 305), lower := (rows 321 35 44 200 146 36 64 128 256), losses := [] }

theorem u6905 : Upper (D 8) (R 8) [320,33,40,192,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6905 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6906 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 321 35 44 200 146 48 101 165 293), lower := (rows 321 35 44 200 146 48 64 128 256), losses := [] }

theorem u6906 : Upper (D 8) (R 8) [320,33,40,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6906 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6907 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 200 176 33 86 150 278), lower := (rows 321 35 44 200 176 33 64 128 256), losses := [] }

theorem u6907 : Upper (D 8) (R 8) [320,33,40,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6908 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 321 35 44 200 176 34 85 149 277), lower := (rows 321 35 44 200 176 34 64 128 256), losses := [] }

theorem u6908 : Upper (D 8) (R 8) [320,33,40,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6908 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6909 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 321 35 44 200 176 36 83 147 275), lower := (rows 321 35 44 200 176 36 64 128 256), losses := [] }

theorem u6909 : Upper (D 8) (R 8) [320,33,40,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6909 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6910 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 321 35 44 200 176 48 71 135 263), lower := (rows 321 35 44 200 176 48 64 128 256), losses := [] }

theorem u6910 : Upper (D 8) (R 8) [320,33,40,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6910 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6911 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 321 35 70 137 148 40 112 176 304), lower := (rows 321 35 70 137 148 40 64 128 256), losses := [] }

theorem u6911 : Upper (D 8) (R 8) [320,33,66,129,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6911 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6912 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 321 35 70 137 148 48 104 168 296), lower := (rows 321 35 70 137 148 48 64 128 256), losses := [] }

theorem u6912 : Upper (D 8) (R 8) [320,33,66,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6912 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6913 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 321 35 70 137 176 36 120 184 312), lower := (rows 321 35 70 137 176 36 64 128 256), losses := [] }

theorem u6913 : Upper (D 8) (R 8) [320,33,66,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6913 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6914 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 321 35 70 137 176 40 116 180 308), lower := (rows 321 35 70 137 176 40 64 128 256), losses := [] }

theorem u6914 : Upper (D 8) (R 8) [320,33,66,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6914 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6915 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 321 35 70 137 176 48 108 172 300), lower := (rows 321 35 70 137 176 48 64 128 256), losses := [] }

theorem u6915 : Upper (D 8) (R 8) [320,33,66,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6915 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6916 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 70 140 176 33 120 184 312), lower := (rows 321 35 70 140 176 33 64 128 256), losses := [] }

theorem u6916 : Upper (D 8) (R 8) [320,33,66,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6917 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 35 70 140 176 40 113 177 305), lower := (rows 321 35 70 140 176 40 64 128 256), losses := [] }

theorem u6917 : Upper (D 8) (R 8) [320,33,66,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6917 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6918 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 321 35 70 140 176 48 105 169 297), lower := (rows 321 35 70 140 176 48 64 128 256), losses := [] }

theorem u6918 : Upper (D 8) (R 8) [320,33,66,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6918 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6919 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 321 35 76 137 146 36 112 176 304), lower := (rows 321 35 76 137 146 36 64 128 256), losses := [] }

theorem u6919 : Upper (D 8) (R 8) [320,33,72,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6919 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6920 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 321 35 76 137 146 48 100 164 292), lower := (rows 321 35 76 137 146 48 64 128 256), losses := [] }

theorem u6920 : Upper (D 8) (R 8) [320,33,72,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6920 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6921 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 321 35 76 137 176 34 116 180 308), lower := (rows 321 35 76 137 176 34 64 128 256), losses := [] }

theorem u6921 : Upper (D 8) (R 8) [320,33,72,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6921 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6922 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 321 35 76 137 176 36 114 178 306), lower := (rows 321 35 76 137 176 36 64 128 256), losses := [] }

theorem u6922 : Upper (D 8) (R 8) [320,33,72,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6922 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6923 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 321 35 76 137 176 48 102 166 294), lower := (rows 321 35 76 137 176 48 64 128 256), losses := [] }

theorem u6923 : Upper (D 8) (R 8) [320,33,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6923 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6924 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 321 35 76 138 145 36 112 176 304), lower := (rows 321 35 76 138 145 36 64 128 256), losses := [] }

theorem u6924 : Upper (D 8) (R 8) [320,33,72,130,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6924 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6925 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 321 35 76 138 145 48 100 164 292), lower := (rows 321 35 76 138 145 48 64 128 256), losses := [] }

theorem u6925 : Upper (D 8) (R 8) [320,33,72,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6925 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6926 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 76 138 176 33 116 180 308), lower := (rows 321 35 76 138 176 33 64 128 256), losses := [] }

theorem u6926 : Upper (D 8) (R 8) [320,33,72,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6927 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 35 76 138 176 36 113 177 305), lower := (rows 321 35 76 138 176 36 64 128 256), losses := [] }

theorem u6927 : Upper (D 8) (R 8) [320,33,72,130,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6927 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6928 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 321 35 76 138 176 48 101 165 293), lower := (rows 321 35 76 138 176 48 64 128 256), losses := [] }

theorem u6928 : Upper (D 8) (R 8) [320,33,72,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6928 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6929 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 321 35 76 168 145 34 116 180 308), lower := (rows 321 35 76 168 145 34 64 128 256), losses := [] }

theorem u6929 : Upper (D 8) (R 8) [320,33,72,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6929 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6930 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 321 35 76 168 145 36 114 178 306), lower := (rows 321 35 76 168 145 36 64 128 256), losses := [] }

theorem u6930 : Upper (D 8) (R 8) [320,33,72,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6930 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6931 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 321 35 76 168 145 48 102 166 294), lower := (rows 321 35 76 168 145 48 64 128 256), losses := [] }

theorem u6931 : Upper (D 8) (R 8) [320,33,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6931 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6932 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 76 168 146 33 116 180 308), lower := (rows 321 35 76 168 146 33 64 128 256), losses := [] }

theorem u6932 : Upper (D 8) (R 8) [320,33,72,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6933 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 35 76 168 146 36 113 177 305), lower := (rows 321 35 76 168 146 36 64 128 256), losses := [] }

theorem u6933 : Upper (D 8) (R 8) [320,33,72,160,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6933 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6934 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 321 35 76 168 146 48 101 165 293), lower := (rows 321 35 76 168 146 48 64 128 256), losses := [] }

theorem u6934 : Upper (D 8) (R 8) [320,33,72,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6934 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6935 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 321 35 100 137 146 36 120 184 312), lower := (rows 321 35 100 137 146 36 64 128 256), losses := [] }

theorem u6935 : Upper (D 8) (R 8) [320,33,96,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6935 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6936 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 321 35 100 137 146 40 116 180 308), lower := (rows 321 35 100 137 146 40 64 128 256), losses := [] }

theorem u6936 : Upper (D 8) (R 8) [320,33,96,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6936 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6937 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 321 35 100 137 146 48 108 172 300), lower := (rows 321 35 100 137 146 48 64 128 256), losses := [] }

theorem u6937 : Upper (D 8) (R 8) [320,33,96,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6937 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6938 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 321 35 100 137 148 34 120 184 312), lower := (rows 321 35 100 137 148 34 64 128 256), losses := [] }

theorem u6938 : Upper (D 8) (R 8) [320,33,96,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6938 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6939 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 321 35 100 137 148 40 114 178 306), lower := (rows 321 35 100 137 148 40 64 128 256), losses := [] }

theorem u6939 : Upper (D 8) (R 8) [320,33,96,129,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6939 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6940 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 321 35 100 137 148 48 106 170 298), lower := (rows 321 35 100 137 148 48 64 128 256), losses := [] }

theorem u6940 : Upper (D 8) (R 8) [320,33,96,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6940 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6941 : PairBound 9 := { available := 28, camps := [], pairs := [], upper := (rows 321 35 100 137 176 34 92 156 284), lower := (rows 321 35 100 137 176 34 64 128 256), losses := [] }

theorem u6941 : Upper (D 8) (R 8) [320,33,96,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6941 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6942 : PairBound 9 := { available := 26, camps := [], pairs := [], upper := (rows 321 35 100 137 176 36 90 154 282), lower := (rows 321 35 100 137 176 36 64 128 256), losses := [] }

theorem u6942 : Upper (D 8) (R 8) [320,33,96,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6942 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6943 : PairBound 9 := { available := 22, camps := [], pairs := [], upper := (rows 321 35 100 137 176 40 86 150 278), lower := (rows 321 35 100 137 176 40 64 128 256), losses := [] }

theorem u6943 : Upper (D 8) (R 8) [320,33,96,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6943 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6944 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 321 35 100 137 176 48 78 142 270), lower := (rows 321 35 100 137 176 48 64 128 256), losses := [] }

theorem u6944 : Upper (D 8) (R 8) [320,33,96,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6944 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6945 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 100 138 148 33 120 184 312), lower := (rows 321 35 100 138 148 33 64 128 256), losses := [] }

theorem u6945 : Upper (D 8) (R 8) [320,33,96,130,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6946 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 321 35 100 138 148 40 113 177 305), lower := (rows 321 35 100 138 148 40 64 128 256), losses := [] }

theorem u6946 : Upper (D 8) (R 8) [320,33,96,130,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6946 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6947 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 321 35 100 138 148 48 105 169 297), lower := (rows 321 35 100 138 148 48 64 128 256), losses := [] }

theorem u6947 : Upper (D 8) (R 8) [320,33,96,130,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6947 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6948 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 100 138 176 33 92 156 284), lower := (rows 321 35 100 138 176 33 64 128 256), losses := [] }

theorem u6948 : Upper (D 8) (R 8) [320,33,96,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6949 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 321 35 100 138 176 36 89 153 281), lower := (rows 321 35 100 138 176 36 64 128 256), losses := [] }

theorem u6949 : Upper (D 8) (R 8) [320,33,96,130,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6949 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6950 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 321 35 100 138 176 40 85 149 277), lower := (rows 321 35 100 138 176 40 64 128 256), losses := [] }

theorem u6950 : Upper (D 8) (R 8) [320,33,96,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6950 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6951 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 321 35 100 138 176 48 77 141 269), lower := (rows 321 35 100 138 176 48 64 128 256), losses := [] }

theorem u6951 : Upper (D 8) (R 8) [320,33,96,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6951 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6952 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 100 140 176 33 90 154 282), lower := (rows 321 35 100 140 176 33 64 128 256), losses := [] }

theorem u6952 : Upper (D 8) (R 8) [320,33,96,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6953 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 321 35 100 140 176 34 89 153 281), lower := (rows 321 35 100 140 176 34 64 128 256), losses := [] }

theorem u6953 : Upper (D 8) (R 8) [320,33,96,132,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6953 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6954 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 321 35 100 140 176 40 83 147 275), lower := (rows 321 35 100 140 176 40 64 128 256), losses := [] }

theorem u6954 : Upper (D 8) (R 8) [320,33,96,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6954 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6955 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 321 35 100 140 176 48 75 139 267), lower := (rows 321 35 100 140 176 48 64 128 256), losses := [] }

theorem u6955 : Upper (D 8) (R 8) [320,33,96,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6955 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6956 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 76 56 145 33 226 162 418), lower := (rows 321 38 76 56 145 33 64 128 256), losses := [] }

theorem u6956 : Upper (D 8) (R 8) [320,36,72,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6957 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 321 38 76 56 145 34 225 161 417), lower := (rows 321 38 76 56 145 34 64 128 256), losses := [] }

theorem u6957 : Upper (D 8) (R 8) [320,36,72,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6957 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6958 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 76 56 145 160 99 163 291), lower := (rows 321 38 76 56 145 160 64 128 256), losses := [] }

theorem u6958 : Upper (D 8) (R 8) [320,36,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6959 : PairBound 9 := { available := 161, camps := [], pairs := [(3,6)], upper := (rows 321 38 76 56 146 33 225 161 417), lower := (rows 321 38 76 56 146 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 10 18 33 0 161 289), good := (rows 417 446 12 440 154 417 0 128 256) }] }

theorem u6959 : Upper (D 8) (R 8) [320,36,72,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6959
end Delivery.IrregularNine14.P08
