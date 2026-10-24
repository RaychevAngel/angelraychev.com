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

def b4980 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 97 38 133 88 176 40 323 387 259), lower := (rows 97 38 133 88 176 40 64 128 256), losses := [] }

theorem u4980 : Upper (D 8) (R 8) [96,36,129,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4980 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4981 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 38 133 88 176 288 75 139 267), lower := (rows 97 38 133 88 176 288 64 128 256), losses := [] }

theorem u4981 : Upper (D 8) (R 8) [96,36,129,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4981 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4982 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 97 38 133 88 273 34 232 168 424), lower := (rows 97 38 133 88 273 34 64 128 256), losses := [] }

theorem u4982 : Upper (D 8) (R 8) [96,36,129,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4982 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4983 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 97 38 133 88 273 40 226 162 418), lower := (rows 97 38 133 88 273 40 64 128 256), losses := [] }

theorem u4983 : Upper (D 8) (R 8) [96,36,129,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4983 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4984 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 88 273 160 106 170 298), lower := (rows 97 38 133 88 273 160 64 128 256), losses := [] }

theorem u4984 : Upper (D 8) (R 8) [96,36,129,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4985 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 88 274 33 232 168 424), lower := (rows 97 38 133 88 274 33 64 128 256), losses := [] }

theorem u4985 : Upper (D 8) (R 8) [96,36,129,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4986 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 133 88 274 40 225 161 417), lower := (rows 97 38 133 88 274 40 64 128 256), losses := [] }

theorem u4986 : Upper (D 8) (R 8) [96,36,129,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4986 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4987 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 88 274 160 105 169 297), lower := (rows 97 38 133 88 274 160 64 128 256), losses := [] }

theorem u4987 : Upper (D 8) (R 8) [96,36,129,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4988 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 88 304 33 202 138 394), lower := (rows 97 38 133 88 304 33 64 128 256), losses := [] }

theorem u4988 : Upper (D 8) (R 8) [96,36,129,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4989 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 38 133 88 304 34 201 137 393), lower := (rows 97 38 133 88 304 34 64 128 256), losses := [] }

theorem u4989 : Upper (D 8) (R 8) [96,36,129,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4989 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4990 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 133 88 304 40 195 131 387), lower := (rows 97 38 133 88 304 40 64 128 256), losses := [] }

theorem u4990 : Upper (D 8) (R 8) [96,36,129,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4990 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4991 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 88 304 160 75 139 267), lower := (rows 97 38 133 88 304 160 64 128 256), losses := [] }

theorem u4991 : Upper (D 8) (R 8) [96,36,129,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4992 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 88 400 33 106 170 298), lower := (rows 97 38 133 88 400 33 64 128 256), losses := [] }

theorem u4992 : Upper (D 8) (R 8) [96,36,129,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4993 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 38 133 88 400 34 105 169 297), lower := (rows 97 38 133 88 400 34 64 128 256), losses := [] }

theorem u4993 : Upper (D 8) (R 8) [96,36,129,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4993 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4994 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 133 88 400 40 99 163 291), lower := (rows 97 38 133 88 400 40 64 128 256), losses := [] }

theorem u4994 : Upper (D 8) (R 8) [96,36,129,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4994 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4995 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 97 38 133 152 273 34 104 232 360), lower := (rows 97 38 133 152 273 34 64 128 256), losses := [] }

theorem u4995 : Upper (D 8) (R 8) [96,36,129,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4995 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4996 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 97 38 133 152 273 40 98 226 354), lower := (rows 97 38 133 152 273 40 64 128 256), losses := [] }

theorem u4996 : Upper (D 8) (R 8) [96,36,129,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4996 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4997 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 152 273 96 106 170 298), lower := (rows 97 38 133 152 273 96 64 128 256), losses := [] }

theorem u4997 : Upper (D 8) (R 8) [96,36,129,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4998 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 152 304 33 74 202 330), lower := (rows 97 38 133 152 304 33 64 128 256), losses := [] }

theorem u4998 : Upper (D 8) (R 8) [96,36,129,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4999 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 38 133 152 304 34 73 201 329), lower := (rows 97 38 133 152 304 34 64 128 256), losses := [] }

theorem u4999 : Upper (D 8) (R 8) [96,36,129,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4999 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5000 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 38 133 152 304 40 67 195 323), lower := (rows 97 38 133 152 304 40 64 128 256), losses := [] }

theorem u5000 : Upper (D 8) (R 8) [96,36,129,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5000 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5001 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 152 304 96 75 139 267), lower := (rows 97 38 133 152 304 96 64 128 256), losses := [] }

theorem u5001 : Upper (D 8) (R 8) [96,36,129,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5002 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 152 336 33 106 170 298), lower := (rows 97 38 133 152 336 33 64 128 256), losses := [] }

theorem u5002 : Upper (D 8) (R 8) [96,36,129,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5003 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 38 133 152 336 34 105 169 297), lower := (rows 97 38 133 152 336 34 64 128 256), losses := [] }

theorem u5003 : Upper (D 8) (R 8) [96,36,129,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5003 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5004 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 133 152 336 40 99 163 291), lower := (rows 97 38 133 152 336 40 64 128 256), losses := [] }

theorem u5004 : Upper (D 8) (R 8) [96,36,129,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5004 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5005 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 97 38 133 168 273 34 88 216 344), lower := (rows 97 38 133 168 273 34 64 128 256), losses := [] }

theorem u5005 : Upper (D 8) (R 8) [96,36,129,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5005 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5006 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 97 38 133 168 273 40 82 210 338), lower := (rows 97 38 133 168 273 40 64 128 256), losses := [] }

theorem u5006 : Upper (D 8) (R 8) [96,36,129,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5006 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5007 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 97 38 133 168 273 48 74 202 330), lower := (rows 97 38 133 168 273 48 64 128 256), losses := [] }

theorem u5007 : Upper (D 8) (R 8) [96,36,129,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5007 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5008 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 168 273 96 90 154 282), lower := (rows 97 38 133 168 273 96 64 128 256), losses := [] }

theorem u5008 : Upper (D 8) (R 8) [96,36,129,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5009 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 168 274 33 88 216 344), lower := (rows 97 38 133 168 274 33 64 128 256), losses := [] }

theorem u5009 : Upper (D 8) (R 8) [96,36,129,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5010 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 38 133 168 274 40 81 209 337), lower := (rows 97 38 133 168 274 40 64 128 256), losses := [] }

theorem u5010 : Upper (D 8) (R 8) [96,36,129,160,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5010 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5011 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 38 133 168 274 48 73 201 329), lower := (rows 97 38 133 168 274 48 64 128 256), losses := [] }

theorem u5011 : Upper (D 8) (R 8) [96,36,129,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5011 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5012 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 168 274 96 89 153 281), lower := (rows 97 38 133 168 274 96 64 128 256), losses := [] }

theorem u5012 : Upper (D 8) (R 8) [96,36,129,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5013 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 168 280 33 82 210 338), lower := (rows 97 38 133 168 280 33 64 128 256), losses := [] }

theorem u5013 : Upper (D 8) (R 8) [96,36,129,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5014 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 38 133 168 280 34 81 209 337), lower := (rows 97 38 133 168 280 34 64 128 256), losses := [] }

theorem u5014 : Upper (D 8) (R 8) [96,36,129,160,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5014 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5015 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 38 133 168 280 48 67 195 323), lower := (rows 97 38 133 168 280 48 64 128 256), losses := [] }

theorem u5015 : Upper (D 8) (R 8) [96,36,129,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5015 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5016 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 168 280 96 83 147 275), lower := (rows 97 38 133 168 280 96 64 128 256), losses := [] }

theorem u5016 : Upper (D 8) (R 8) [96,36,129,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5017 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 168 336 33 90 154 282), lower := (rows 97 38 133 168 336 33 64 128 256), losses := [] }

theorem u5017 : Upper (D 8) (R 8) [96,36,129,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5018 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 38 133 168 336 34 89 153 281), lower := (rows 97 38 133 168 336 34 64 128 256), losses := [] }

theorem u5018 : Upper (D 8) (R 8) [96,36,129,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5018 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5019 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 38 133 168 336 40 83 147 275), lower := (rows 97 38 133 168 336 40 64 128 256), losses := [] }

theorem u5019 : Upper (D 8) (R 8) [96,36,129,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5019 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5020 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 38 133 168 336 48 75 139 267), lower := (rows 97 38 133 168 336 48 64 128 256), losses := [] }

theorem u5020 : Upper (D 8) (R 8) [96,36,129,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5020 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5021 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 97 38 133 200 273 34 120 184 312), lower := (rows 97 38 133 200 273 34 64 128 256), losses := [] }

theorem u5021 : Upper (D 8) (R 8) [96,36,129,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5021 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5022 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 97 38 133 200 273 40 114 178 306), lower := (rows 97 38 133 200 273 40 64 128 256), losses := [] }

theorem u5022 : Upper (D 8) (R 8) [96,36,129,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5022 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5023 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 97 38 133 200 273 48 106 170 298), lower := (rows 97 38 133 200 273 48 64 128 256), losses := [] }

theorem u5023 : Upper (D 8) (R 8) [96,36,129,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5023 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5024 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 200 274 33 120 184 312), lower := (rows 97 38 133 200 274 33 64 128 256), losses := [] }

theorem u5024 : Upper (D 8) (R 8) [96,36,129,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5025 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 133 200 274 40 113 177 305), lower := (rows 97 38 133 200 274 40 64 128 256), losses := [] }

theorem u5025 : Upper (D 8) (R 8) [96,36,129,192,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5025 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5026 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 38 133 200 274 48 105 169 297), lower := (rows 97 38 133 200 274 48 64 128 256), losses := [] }

theorem u5026 : Upper (D 8) (R 8) [96,36,129,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5026 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5027 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 200 280 33 114 178 306), lower := (rows 97 38 133 200 280 33 64 128 256), losses := [] }

theorem u5027 : Upper (D 8) (R 8) [96,36,129,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5028 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 133 200 280 34 113 177 305), lower := (rows 97 38 133 200 280 34 64 128 256), losses := [] }

theorem u5028 : Upper (D 8) (R 8) [96,36,129,192,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5028 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5029 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 133 200 280 48 99 163 291), lower := (rows 97 38 133 200 280 48 64 128 256), losses := [] }

theorem u5029 : Upper (D 8) (R 8) [96,36,129,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5029 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5030 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 200 304 33 90 154 282), lower := (rows 97 38 133 200 304 33 64 128 256), losses := [] }

theorem u5030 : Upper (D 8) (R 8) [96,36,129,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5031 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 38 133 200 304 34 89 153 281), lower := (rows 97 38 133 200 304 34 64 128 256), losses := [] }

theorem u5031 : Upper (D 8) (R 8) [96,36,129,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5031 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5032 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 38 133 200 304 40 83 147 275), lower := (rows 97 38 133 200 304 40 64 128 256), losses := [] }

theorem u5032 : Upper (D 8) (R 8) [96,36,129,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5032 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5033 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 38 133 200 304 48 75 139 267), lower := (rows 97 38 133 200 304 48 64 128 256), losses := [] }

theorem u5033 : Upper (D 8) (R 8) [96,36,129,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5033 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5034 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 134 56 273 33 200 200 456), lower := (rows 97 38 134 56 273 33 64 128 256), losses := [] }

theorem u5034 : Upper (D 8) (R 8) [96,36,130,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5035 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 38 134 56 273 40 193 193 449), lower := (rows 97 38 134 56 273 40 64 128 256), losses := [] }

theorem u5035 : Upper (D 8) (R 8) [96,36,130,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5035 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5036 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 134 56 273 96 201 137 393), lower := (rows 97 38 134 56 273 96 64 128 256), losses := [] }

theorem u5036 : Upper (D 8) (R 8) [96,36,130,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5037 : PairBound 9 := { available := 73, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 134 56 273 160 73 201 329), lower := (rows 97 38 134 56 273 160 64 128 256), losses := [] }

theorem u5037 : Upper (D 8) (R 8) [96,36,130,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5038 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 56 280 33 193 193 449), lower := (rows 97 38 134 56 280 33 64 128 256), losses := [] }

theorem u5038 : Upper (D 8) (R 8) [96,36,130,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5039 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 134 56 280 96 193 129 385), lower := (rows 97 38 134 56 280 96 64 128 256), losses := [] }

theorem u5039 : Upper (D 8) (R 8) [96,36,130,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5039
end Delivery.IrregularNine14.P08
