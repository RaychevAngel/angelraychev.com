import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0008

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6900 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 7 137 336 48 192 162 290), lower := (rows 37 74 7 137 336 48 192 128 256), losses := [] }

theorem u6900 : Upper (D 7) (R 7) [36,72,3,129,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6900 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6901 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 74 7 137 400 48 66 224 352), lower := (rows 37 74 7 137 400 48 66 128 256), losses := [] }

theorem u6901 : Upper (D 7) (R 7) [36,72,3,129,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6901 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6902 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 74 7 137 400 48 96 194 322), lower := (rows 37 74 7 137 400 48 96 128 256), losses := [] }

theorem u6902 : Upper (D 7) (R 7) [36,72,3,129,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6902 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6903 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 7 138 112 288 65 144 400), lower := (rows 37 74 7 138 112 288 65 128 256), losses := [] }

theorem u6903 : Upper (D 7) (R 7) [36,72,3,130,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6903 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6904 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 74 7 138 112 288 80 129 385), lower := (rows 37 74 7 138 112 288 80 128 256), losses := [] }

theorem u6904 : Upper (D 7) (R 7) [36,72,3,130,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6904 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6905 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 7 138 112 288 192 145 273), lower := (rows 37 74 7 138 112 288 192 128 256), losses := [] }

theorem u6905 : Upper (D 7) (R 7) [36,72,3,130,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6905 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6906 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 7 138 176 288 65 208 336), lower := (rows 37 74 7 138 176 288 65 128 256), losses := [] }

theorem u6906 : Upper (D 7) (R 7) [36,72,3,130,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6906 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6907 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 37 74 7 138 176 288 80 193 321), lower := (rows 37 74 7 138 176 288 80 128 256), losses := [] }

theorem u6907 : Upper (D 7) (R 7) [36,72,3,130,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6907 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6908 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 7 138 400 48 65 224 352), lower := (rows 37 74 7 138 400 48 65 128 256), losses := [] }

theorem u6908 : Upper (D 7) (R 7) [36,72,3,130,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6908 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6909 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,1),(1,0),(4,1)], upper := (rows 37 74 7 138 400 48 96 193 321), lower := (rows 37 74 7 138 400 48 96 128 256), losses := [] }

theorem u6909 : Upper (D 7) (R 7) [36,72,3,130,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6909 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6910 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 7 152 112 288 65 130 386), lower := (rows 37 74 7 152 112 288 65 128 256), losses := [] }

theorem u6910 : Upper (D 7) (R 7) [36,72,3,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6910 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6911 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 7 152 112 288 66 129 385), lower := (rows 37 74 7 152 112 288 66 128 256), losses := [] }

theorem u6911 : Upper (D 7) (R 7) [36,72,3,144,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6911 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6912 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 7 152 112 288 192 131 259), lower := (rows 37 74 7 152 112 288 192 128 256), losses := [] }

theorem u6912 : Upper (D 7) (R 7) [36,72,3,144,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6912 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6913 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 74 7 152 304 160 65 194 322), lower := (rows 37 74 7 152 304 160 65 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 168 0 128 256), good := (rows 37 47 7 184 304 160 1 160 256) }] }

theorem u6913 : Upper (D 7) (R 7) [36,72,3,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6914 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 160 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,6),(1,0),(1,5),(1,7)], upper := (rows 37 74 7 152 304 160 66 193 321), lower := (rows 37 74 7 152 304 160 66 128 256), losses := [{ target := 6, region := (rows 3 2 70 8 16 168 0 128 256), good := (rows 37 47 7 184 304 160 7 160 256) }] }

theorem u6914 : Upper (D 7) (R 7) [36,72,3,144,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6915 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 74 7 152 336 160 65 162 290), lower := (rows 37 74 7 152 336 160 65 128 256), losses := [] }

theorem u6915 : Upper (D 7) (R 7) [36,72,3,144,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6916 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 3, region := 66, targets := 160 }], pairs := [(0,6),(1,5),(1,7),(2,6)], upper := (rows 37 74 7 152 336 160 66 161 289), lower := (rows 37 74 7 152 336 160 66 128 256), losses := [] }

theorem u6916 : Upper (D 7) (R 7) [36,72,3,144,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6917 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,7)], upper := (rows 37 74 7 152 336 160 96 131 259), lower := (rows 37 74 7 152 336 160 96 128 256), losses := [{ target := 7, region := (rows 1 2 4 8 21 32 97 0 260), good := (rows 373 74 343 24 336 96 96 0 256) }] }

theorem u6917 : Upper (D 7) (R 7) [36,72,3,144,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6918 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 168 208 288 65 146 274), lower := (rows 37 74 7 168 208 288 65 128 256), losses := [] }

theorem u6918 : Upper (D 7) (R 7) [36,72,3,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6918 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6919 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 74 7 168 208 288 66 145 273), lower := (rows 37 74 7 168 208 288 66 128 256), losses := [] }

theorem u6919 : Upper (D 7) (R 7) [36,72,3,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6919 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6920 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 82, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 37 74 7 168 208 288 80 131 259), lower := (rows 37 74 7 168 208 288 80 128 256), losses := [] }

theorem u6920 : Upper (D 7) (R 7) [36,72,3,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6920 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6921 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 168 336 48 65 130 386), lower := (rows 37 74 7 168 336 48 65 128 256), losses := [] }

theorem u6921 : Upper (D 7) (R 7) [36,72,3,160,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6921 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6922 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 168 336 48 66 129 385), lower := (rows 37 74 7 168 336 48 66 128 256), losses := [] }

theorem u6922 : Upper (D 7) (R 7) [36,72,3,160,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6922 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6923 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 7 168 336 48 192 131 259), lower := (rows 37 74 7 168 336 48 192 128 256), losses := [] }

theorem u6923 : Upper (D 7) (R 7) [36,72,3,160,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6923 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6924 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 37 74 7 265 112 160 66 144 400), lower := (rows 37 74 7 265 112 160 66 128 256), losses := [] }

theorem u6924 : Upper (D 7) (R 7) [36,72,3,257,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6925 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 74 7 265 112 160 80 130 386), lower := (rows 37 74 7 265 112 160 80 128 256), losses := [] }

theorem u6925 : Upper (D 7) (R 7) [36,72,3,257,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6925 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6926 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 7 265 112 160 192 146 274), lower := (rows 37 74 7 265 112 160 192 128 256), losses := [] }

theorem u6926 : Upper (D 7) (R 7) [36,72,3,257,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6927 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 74 7 265 208 48 66 160 416), lower := (rows 37 74 7 265 208 48 66 128 256), losses := [] }

theorem u6927 : Upper (D 7) (R 7) [36,72,3,257,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6927 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6928 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 392, targets := 96 },{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0),(3,5),(3,6)], upper := (rows 37 74 7 265 208 48 96 130 386), lower := (rows 37 74 7 265 208 48 96 128 256), losses := [] }

theorem u6928 : Upper (D 7) (R 7) [36,72,3,257,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6928 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6929 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 265 208 48 192 162 290), lower := (rows 37 74 7 265 208 48 192 128 256), losses := [] }

theorem u6929 : Upper (D 7) (R 7) [36,72,3,257,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6929 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6930 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 37 74 7 265 208 160 66 176 304), lower := (rows 37 74 7 265 208 160 66 128 256), losses := [] }

theorem u6930 : Upper (D 7) (R 7) [36,72,3,257,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6931 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 74 7 265 208 160 80 162 290), lower := (rows 37 74 7 265 208 160 80 128 256), losses := [] }

theorem u6931 : Upper (D 7) (R 7) [36,72,3,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6931 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6932 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 1, region := 144, targets := 32 },{ cop := 5, region := 80, targets := 2 }], pairs := [(1,0),(4,0),(4,1),(4,5)], upper := (rows 37 74 7 265 208 160 96 146 274), lower := (rows 37 74 7 265 208 160 96 128 256), losses := [] }

theorem u6932 : Upper (D 7) (R 7) [36,72,3,257,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6933 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 74 7 266 112 160 65 144 400), lower := (rows 37 74 7 266 112 160 65 128 256), losses := [] }

theorem u6933 : Upper (D 7) (R 7) [36,72,3,258,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6934 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 74 7 266 112 160 80 129 385), lower := (rows 37 74 7 266 112 160 80 128 256), losses := [] }

theorem u6934 : Upper (D 7) (R 7) [36,72,3,258,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6934 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6935 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 7 266 112 160 192 145 273), lower := (rows 37 74 7 266 112 160 192 128 256), losses := [] }

theorem u6935 : Upper (D 7) (R 7) [36,72,3,258,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6936 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 74 7 266 208 160 65 176 304), lower := (rows 37 74 7 266 208 160 65 128 256), losses := [] }

theorem u6936 : Upper (D 7) (R 7) [36,72,3,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6937 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 74 7 266 208 160 80 161 289), lower := (rows 37 74 7 266 208 160 80 128 256), losses := [] }

theorem u6937 : Upper (D 7) (R 7) [36,72,3,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6937 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6938 : Route 9 := (fun mask => (mask,id))

def c6938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6938 : Upper (D 7) (R 7) [36,72,3,258,192,128,32] 13 := by
  apply FastRouting.sound _ _ [36,72,3,258,192,128,32] 13 (by decide) (choices 1) [1,16] r6938 c6938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u508
  · exact u509

def b6939 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 37 74 7 280 112 160 65 130 386), lower := (rows 37 74 7 280 112 160 65 128 256), losses := [] }

theorem u6939 : Upper (D 7) (R 7) [36,72,3,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6940 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 66, targets := 161 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(1,7)], upper := (rows 37 74 7 280 112 160 66 129 385), lower := (rows 37 74 7 280 112 160 66 128 256), losses := [] }

theorem u6940 : Upper (D 7) (R 7) [36,72,3,272,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6941 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 7 280 112 160 192 131 259), lower := (rows 37 74 7 280 112 160 192 128 256), losses := [] }

theorem u6941 : Upper (D 7) (R 7) [36,72,3,272,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6942 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 66, targets := 160 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 7 280 145 160 66 224 352), lower := (rows 37 74 7 280 145 160 66 128 256), losses := [] }

theorem u6942 : Upper (D 7) (R 7) [36,72,3,272,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6943 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(3,5),(4,5)], upper := (rows 37 74 7 280 145 160 96 194 322), lower := (rows 37 74 7 280 145 160 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 20 0 64 130 258), good := (rows 29 458 415 280 145 128 64 128 256) }] }

theorem u6943 : Upper (D 7) (R 7) [36,72,3,272,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6944 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 74 7 280 146 160 65 224 352), lower := (rows 37 74 7 280 146 160 65 128 256), losses := [] }

theorem u6944 : Upper (D 7) (R 7) [36,72,3,272,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6945 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 37, targets := 64 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,6),(1,0),(2,6)], upper := (rows 37 74 7 280 146 160 96 193 321), lower := (rows 37 74 7 280 146 160 96 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 249 128 256), good := (rows 100 74 70 378 242 224 96 224 256) }] }

theorem u6945 : Upper (D 7) (R 7) [36,72,3,272,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6946 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 74 7 280 208 160 65 162 290), lower := (rows 37 74 7 280 208 160 65 128 256), losses := [] }

theorem u6946 : Upper (D 7) (R 7) [36,72,3,272,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6947 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 161 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(1,7)], upper := (rows 37 74 7 280 208 160 66 161 289), lower := (rows 37 74 7 280 208 160 66 128 256), losses := [] }

theorem u6947 : Upper (D 7) (R 7) [36,72,3,272,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6948 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 37 74 7 280 208 160 96 131 259), lower := (rows 37 74 7 280 208 160 96 128 256), losses := [] }

theorem u6948 : Upper (D 7) (R 7) [36,72,3,272,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6949 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 7 296 81 160 66 144 400), lower := (rows 37 74 7 296 81 160 66 128 256), losses := [] }

theorem u6949 : Upper (D 7) (R 7) [36,72,3,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6950 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 296 81 160 80 130 386), lower := (rows 37 74 7 296 81 160 80 128 256), losses := [] }

theorem u6950 : Upper (D 7) (R 7) [36,72,3,288,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6950 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6951 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 37 74 7 296 81 160 192 146 274), lower := (rows 37 74 7 296 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 224 224 128 256), good := (rows 117 104 21 360 113 224 224 224 256) }] }

theorem u6951 : Upper (D 7) (R 7) [36,72,3,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6952 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 74 7 296 145 160 66 208 336), lower := (rows 37 74 7 296 145 160 66 128 256), losses := [] }

theorem u6952 : Upper (D 7) (R 7) [36,72,3,288,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6953 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 37 74 7 296 145 160 80 194 322), lower := (rows 37 74 7 296 145 160 80 128 256), losses := [] }

theorem u6953 : Upper (D 7) (R 7) [36,72,3,288,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6953 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6954 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 442, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 74 7 296 146 160 65 208 336), lower := (rows 37 74 7 296 146 160 65 128 256), losses := [] }

theorem u6954 : Upper (D 7) (R 7) [36,72,3,288,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6955 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 37, targets := 64 },{ cop := 2, region := 208, targets := 32 }], pairs := [(0,6),(2,6),(4,5)], upper := (rows 37 74 7 296 146 160 80 193 321), lower := (rows 37 74 7 296 146 160 80 128 256), losses := [] }

theorem u6955 : Upper (D 7) (R 7) [36,72,3,288,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6955 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6956 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 296 208 48 65 130 386), lower := (rows 37 74 7 296 208 48 65 128 256), losses := [] }

theorem u6956 : Upper (D 7) (R 7) [36,72,3,288,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6956 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6957 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 296 208 48 66 129 385), lower := (rows 37 74 7 296 208 48 66 128 256), losses := [] }

theorem u6957 : Upper (D 7) (R 7) [36,72,3,288,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6957 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6958 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 296 208 48 192 131 259), lower := (rows 37 74 7 296 208 48 192 128 256), losses := [] }

theorem u6958 : Upper (D 7) (R 7) [36,72,3,288,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6958 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6959 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 442, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 74 7 296 208 160 65 146 274), lower := (rows 37 74 7 296 208 160 65 128 256), losses := [] }

theorem u6959 : Upper (D 7) (R 7) [36,72,3,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6959
end Delivery.IrregularNine14.P07
