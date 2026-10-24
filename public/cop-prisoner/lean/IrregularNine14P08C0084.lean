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

def b5040 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 134 56 280 160 65 193 321), lower := (rows 97 38 134 56 280 160 64 128 256), losses := [] }

theorem u5040 : Upper (D 8) (R 8) [96,36,130,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5041 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 56 336 33 201 137 393), lower := (rows 97 38 134 56 336 33 64 128 256), losses := [] }

theorem u5041 : Upper (D 8) (R 8) [96,36,130,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5042 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 134 56 336 40 193 129 385), lower := (rows 97 38 134 56 336 40 64 128 256), losses := [] }

theorem u5042 : Upper (D 8) (R 8) [96,36,130,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5042 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5043 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 134 56 336 160 73 137 265), lower := (rows 97 38 134 56 336 160 64 128 256), losses := [] }

theorem u5043 : Upper (D 8) (R 8) [96,36,130,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5044 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 88 273 33 232 168 424), lower := (rows 97 38 134 88 273 33 64 128 256), losses := [] }

theorem u5044 : Upper (D 8) (R 8) [96,36,130,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5045 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 134 88 273 40 225 161 417), lower := (rows 97 38 134 88 273 40 64 128 256), losses := [] }

theorem u5045 : Upper (D 8) (R 8) [96,36,130,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5045 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5046 : PairBound 9 := { available := 41, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 134 88 273 160 105 169 297), lower := (rows 97 38 134 88 273 160 64 128 256), losses := [] }

theorem u5046 : Upper (D 8) (R 8) [96,36,130,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5047 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 134 88 304 33 201 137 393), lower := (rows 97 38 134 88 304 33 64 128 256), losses := [] }

theorem u5047 : Upper (D 8) (R 8) [96,36,130,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5048 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 134 88 304 40 193 129 385), lower := (rows 97 38 134 88 304 40 64 128 256), losses := [] }

theorem u5048 : Upper (D 8) (R 8) [96,36,130,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5048 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5049 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 134 88 304 160 73 137 265), lower := (rows 97 38 134 88 304 160 64 128 256), losses := [] }

theorem u5049 : Upper (D 8) (R 8) [96,36,130,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5050 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 140 56 273 33 194 194 450), lower := (rows 97 38 140 56 273 33 64 128 256), losses := [] }

theorem u5050 : Upper (D 8) (R 8) [96,36,136,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5051 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 38 140 56 273 34 193 193 449), lower := (rows 97 38 140 56 273 34 64 128 256), losses := [] }

theorem u5051 : Upper (D 8) (R 8) [96,36,136,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5051 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5052 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 56 273 96 195 131 387), lower := (rows 97 38 140 56 273 96 64 128 256), losses := [] }

theorem u5052 : Upper (D 8) (R 8) [96,36,136,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5053 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 56 273 160 67 195 323), lower := (rows 97 38 140 56 273 160 64 128 256), losses := [] }

theorem u5053 : Upper (D 8) (R 8) [96,36,136,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5054 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 56 274 33 193 193 449), lower := (rows 97 38 140 56 274 33 64 128 256), losses := [] }

theorem u5054 : Upper (D 8) (R 8) [96,36,136,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5055 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 56 274 96 193 129 385), lower := (rows 97 38 140 56 274 96 64 128 256), losses := [] }

theorem u5055 : Upper (D 8) (R 8) [96,36,136,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5056 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 56 274 160 65 193 321), lower := (rows 97 38 140 56 274 160 64 128 256), losses := [] }

theorem u5056 : Upper (D 8) (R 8) [96,36,136,48,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5057 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 56 336 33 195 131 387), lower := (rows 97 38 140 56 336 33 64 128 256), losses := [] }

theorem u5057 : Upper (D 8) (R 8) [96,36,136,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5058 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 140 56 336 34 193 129 385), lower := (rows 97 38 140 56 336 34 64 128 256), losses := [] }

theorem u5058 : Upper (D 8) (R 8) [96,36,136,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5058 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5059 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 56 336 160 67 131 259), lower := (rows 97 38 140 56 336 160 64 128 256), losses := [] }

theorem u5059 : Upper (D 8) (R 8) [96,36,136,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5060 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 273 33 226 162 418), lower := (rows 97 38 140 88 273 33 64 128 256), losses := [] }

theorem u5060 : Upper (D 8) (R 8) [96,36,136,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5061 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 140 88 273 34 225 161 417), lower := (rows 97 38 140 88 273 34 64 128 256), losses := [] }

theorem u5061 : Upper (D 8) (R 8) [96,36,136,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5061 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5062 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 273 160 99 163 291), lower := (rows 97 38 140 88 273 160 64 128 256), losses := [] }

theorem u5062 : Upper (D 8) (R 8) [96,36,136,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5063 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 274 33 225 161 417), lower := (rows 97 38 140 88 274 33 64 128 256), losses := [] }

theorem u5063 : Upper (D 8) (R 8) [96,36,136,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5064 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 274 160 97 161 289), lower := (rows 97 38 140 88 274 160 64 128 256), losses := [] }

theorem u5064 : Upper (D 8) (R 8) [96,36,136,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5065 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 304 33 195 131 387), lower := (rows 97 38 140 88 304 33 64 128 256), losses := [] }

theorem u5065 : Upper (D 8) (R 8) [96,36,136,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5066 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 140 88 304 34 193 129 385), lower := (rows 97 38 140 88 304 34 64 128 256), losses := [] }

theorem u5066 : Upper (D 8) (R 8) [96,36,136,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5066 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5067 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 304 160 67 131 259), lower := (rows 97 38 140 88 304 160 64 128 256), losses := [] }

theorem u5067 : Upper (D 8) (R 8) [96,36,136,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5068 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 140 265 82 33 240 176 432), lower := (rows 97 38 140 265 82 33 64 128 256), losses := [] }

theorem u5068 : Upper (D 8) (R 8) [96,36,136,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5069 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 140 265 82 48 225 161 417), lower := (rows 97 38 140 265 82 48 64 128 256), losses := [] }

theorem u5069 : Upper (D 8) (R 8) [96,36,136,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5069 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5070 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 265 82 160 113 177 305), lower := (rows 97 38 140 265 82 160 64 128 256), losses := [] }

theorem u5070 : Upper (D 8) (R 8) [96,36,136,257,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5071 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 97 38 140 265 145 34 112 240 368), lower := (rows 97 38 140 265 145 34 64 128 256), losses := [] }

theorem u5071 : Upper (D 8) (R 8) [96,36,136,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5071 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5072 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 97 38 140 265 145 48 98 226 354), lower := (rows 97 38 140 265 145 48 64 128 256), losses := [] }

theorem u5072 : Upper (D 8) (R 8) [96,36,136,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5072 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5073 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 265 145 96 114 178 306), lower := (rows 97 38 140 265 145 96 64 128 256), losses := [] }

theorem u5073 : Upper (D 8) (R 8) [96,36,136,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5074 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 140 265 176 33 82 210 338), lower := (rows 97 38 140 265 176 33 64 128 256), losses := [] }

theorem u5074 : Upper (D 8) (R 8) [96,36,136,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5075 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 38 140 265 176 34 81 209 337), lower := (rows 97 38 140 265 176 34 64 128 256), losses := [] }

theorem u5075 : Upper (D 8) (R 8) [96,36,136,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5075 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5076 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 38 140 265 176 48 67 195 323), lower := (rows 97 38 140 265 176 48 64 128 256), losses := [] }

theorem u5076 : Upper (D 8) (R 8) [96,36,136,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5076 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5077 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 265 176 96 83 147 275), lower := (rows 97 38 140 265 176 96 64 128 256), losses := [] }

theorem u5077 : Upper (D 8) (R 8) [96,36,136,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5078 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 140 265 208 33 114 178 306), lower := (rows 97 38 140 265 208 33 64 128 256), losses := [] }

theorem u5078 : Upper (D 8) (R 8) [96,36,136,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5079 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 140 265 208 34 113 177 305), lower := (rows 97 38 140 265 208 34 64 128 256), losses := [] }

theorem u5079 : Upper (D 8) (R 8) [96,36,136,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5079 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5080 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 140 265 208 48 99 163 291), lower := (rows 97 38 140 265 208 48 64 128 256), losses := [] }

theorem u5080 : Upper (D 8) (R 8) [96,36,136,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5080 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5081 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 280 82 33 225 161 417), lower := (rows 97 38 140 280 82 33 64 128 256), losses := [] }

theorem u5081 : Upper (D 8) (R 8) [96,36,136,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5082 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 280 82 160 97 161 289), lower := (rows 97 38 140 280 82 160 64 128 256), losses := [] }

theorem u5082 : Upper (D 8) (R 8) [96,36,136,272,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5083 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 296 82 33 209 145 401), lower := (rows 97 38 140 296 82 33 64 128 256), losses := [] }

theorem u5083 : Upper (D 8) (R 8) [96,36,136,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5084 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 140 296 82 48 193 129 385), lower := (rows 97 38 140 296 82 48 64 128 256), losses := [] }

theorem u5084 : Upper (D 8) (R 8) [96,36,136,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5084 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5085 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 296 82 160 81 145 273), lower := (rows 97 38 140 296 82 160 64 128 256), losses := [] }

theorem u5085 : Upper (D 8) (R 8) [96,36,136,288,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5086 : PairBound 9 := { available := 82, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 296 145 33 82 210 338), lower := (rows 97 38 140 296 145 33 64 128 256), losses := [] }

theorem u5086 : Upper (D 8) (R 8) [96,36,136,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5087 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 38 140 296 145 34 81 209 337), lower := (rows 97 38 140 296 145 34 64 128 256), losses := [] }

theorem u5087 : Upper (D 8) (R 8) [96,36,136,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5087 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5088 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 38 140 296 145 48 67 195 323), lower := (rows 97 38 140 296 145 48 64 128 256), losses := [] }

theorem u5088 : Upper (D 8) (R 8) [96,36,136,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5088 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5089 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 296 145 96 83 147 275), lower := (rows 97 38 140 296 145 96 64 128 256), losses := [] }

theorem u5089 : Upper (D 8) (R 8) [96,36,136,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5090 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 296 208 33 83 147 275), lower := (rows 97 38 140 296 208 33 64 128 256), losses := [] }

theorem u5090 : Upper (D 8) (R 8) [96,36,136,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5091 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 140 296 208 34 81 145 273), lower := (rows 97 38 140 296 208 34 64 128 256), losses := [] }

theorem u5091 : Upper (D 8) (R 8) [96,36,136,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5091 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5092 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 140 296 208 48 67 131 259), lower := (rows 97 38 140 296 208 48 64 128 256), losses := [] }

theorem u5092 : Upper (D 8) (R 8) [96,36,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5092 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5093 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 328 145 33 114 178 306), lower := (rows 97 38 140 328 145 33 64 128 256), losses := [] }

theorem u5093 : Upper (D 8) (R 8) [96,36,136,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5094 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 140 328 145 34 113 177 305), lower := (rows 97 38 140 328 145 34 64 128 256), losses := [] }

theorem u5094 : Upper (D 8) (R 8) [96,36,136,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5094 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5095 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 140 328 145 48 99 163 291), lower := (rows 97 38 140 328 145 48 64 128 256), losses := [] }

theorem u5095 : Upper (D 8) (R 8) [96,36,136,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5095 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5096 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 328 176 33 83 147 275), lower := (rows 97 38 140 328 176 33 64 128 256), losses := [] }

theorem u5096 : Upper (D 8) (R 8) [96,36,136,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5097 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 140 328 176 34 81 145 273), lower := (rows 97 38 140 328 176 34 64 128 256), losses := [] }

theorem u5097 : Upper (D 8) (R 8) [96,36,136,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5097 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5098 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 140 328 176 48 67 131 259), lower := (rows 97 38 140 328 176 48 64 128 256), losses := [] }

theorem u5098 : Upper (D 8) (R 8) [96,36,136,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5098 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5099 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 56 273 33 202 138 394), lower := (rows 97 38 196 56 273 33 64 128 256), losses := [] }

theorem u5099 : Upper (D 8) (R 8) [96,36,192,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5099
end Delivery.IrregularNine14.P08
