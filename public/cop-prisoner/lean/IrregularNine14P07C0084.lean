import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5040 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 152 336 40 66 164 292), lower := (rows 35 67 133 152 336 40 66 128 256), losses := [] }

theorem u5040 : Upper (D 7) (R 7) [34,65,129,144,320,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5040 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5041 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 152 336 40 68 162 290), lower := (rows 35 67 133 152 336 40 68 128 256), losses := [] }

theorem u5041 : Upper (D 7) (R 7) [34,65,129,144,320,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5041 [(5,3),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5042 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 152 336 40 96 134 262), lower := (rows 35 67 133 152 336 40 96 128 256), losses := [] }

theorem u5042 : Upper (D 7) (R 7) [34,65,129,144,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5042 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5043 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 200 274 36 72 176 304), lower := (rows 35 67 133 200 274 36 72 128 256), losses := [] }

theorem u5043 : Upper (D 7) (R 7) [34,65,129,192,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5043 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5044 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 200 274 36 80 168 296), lower := (rows 35 67 133 200 274 36 80 128 256), losses := [] }

theorem u5044 : Upper (D 7) (R 7) [34,65,129,192,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5044 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5045 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 200 274 36 96 152 280), lower := (rows 35 67 133 200 274 36 96 128 256), losses := [] }

theorem u5045 : Upper (D 7) (R 7) [34,65,129,192,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5045 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5046 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 200 276 48 66 168 296), lower := (rows 35 67 133 200 276 48 66 128 256), losses := [] }

theorem u5046 : Upper (D 7) (R 7) [34,65,129,192,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5046 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5047 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 200 276 48 72 162 290), lower := (rows 35 67 133 200 276 48 72 128 256), losses := [] }

theorem u5047 : Upper (D 7) (R 7) [34,65,129,192,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5047 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5048 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 200 276 48 96 138 266), lower := (rows 35 67 133 200 276 48 96 128 256), losses := [] }

theorem u5048 : Upper (D 7) (R 7) [34,65,129,192,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5048 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5049 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 200 280 36 66 176 304), lower := (rows 35 67 133 200 280 36 66 128 256), losses := [] }

theorem u5049 : Upper (D 7) (R 7) [34,65,129,192,264,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5049 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5050 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 200 280 36 80 162 290), lower := (rows 35 67 133 200 280 36 80 128 256), losses := [] }

theorem u5050 : Upper (D 7) (R 7) [34,65,129,192,264,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5050 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5051 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 200 280 36 96 146 274), lower := (rows 35 67 133 200 280 36 96 128 256), losses := [] }

theorem u5051 : Upper (D 7) (R 7) [34,65,129,192,264,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5051 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5052 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 200 280 48 66 164 292), lower := (rows 35 67 133 200 280 48 66 128 256), losses := [] }

theorem u5052 : Upper (D 7) (R 7) [34,65,129,192,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5052 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5053 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 307, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 133 200 280 48 68 162 290), lower := (rows 35 67 133 200 280 48 68 128 256), losses := [] }

theorem u5053 : Upper (D 7) (R 7) [34,65,129,192,264,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5053 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5054 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 200 280 48 96 134 262), lower := (rows 35 67 133 200 280 48 96 128 256), losses := [] }

theorem u5054 : Upper (D 7) (R 7) [34,65,129,192,264,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5054 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5055 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 200 304 36 66 152 280), lower := (rows 35 67 133 200 304 36 66 128 256), losses := [] }

theorem u5055 : Upper (D 7) (R 7) [34,65,129,192,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5055 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5056 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 200 304 36 72 146 274), lower := (rows 35 67 133 200 304 36 72 128 256), losses := [] }

theorem u5056 : Upper (D 7) (R 7) [34,65,129,192,288,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5056 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5057 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 133 200 304 36 80 138 266), lower := (rows 35 67 133 200 304 36 80 128 256), losses := [] }

theorem u5057 : Upper (D 7) (R 7) [34,65,129,192,288,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5057 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5058 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 265 208 36 66 176 304), lower := (rows 35 67 140 265 208 36 66 128 256), losses := [] }

theorem u5058 : Upper (D 7) (R 7) [34,65,136,257,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5058 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5059 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 140 265 208 36 80 162 290), lower := (rows 35 67 140 265 208 36 80 128 256), losses := [] }

theorem u5059 : Upper (D 7) (R 7) [34,65,136,257,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5059 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5060 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 140 265 208 36 96 146 274), lower := (rows 35 67 140 265 208 36 96 128 256), losses := [] }

theorem u5060 : Upper (D 7) (R 7) [34,65,136,257,192,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5060 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5061 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 296 208 36 65 146 274), lower := (rows 35 67 140 296 208 36 65 128 256), losses := [] }

theorem u5061 : Upper (D 7) (R 7) [34,65,136,288,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5061 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5062 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 296 208 36 66 145 273), lower := (rows 35 67 140 296 208 36 66 128 256), losses := [] }

theorem u5062 : Upper (D 7) (R 7) [34,65,136,288,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5062 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5063 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 140 296 208 36 80 131 259), lower := (rows 35 67 140 296 208 36 80 128 256), losses := [] }

theorem u5063 : Upper (D 7) (R 7) [34,65,136,288,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5063 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5064 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 200 273 48 66 140 268), lower := (rows 35 67 164 200 273 48 66 128 256), losses := [] }

theorem u5064 : Upper (D 7) (R 7) [34,65,160,192,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5064 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5065 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 164 200 273 48 68 138 266), lower := (rows 35 67 164 200 273 48 68 128 256), losses := [] }

theorem u5065 : Upper (D 7) (R 7) [34,65,160,192,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5065 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5066 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 164 200 273 48 72 134 262), lower := (rows 35 67 164 200 273 48 72 128 256), losses := [] }

theorem u5066 : Upper (D 7) (R 7) [34,65,160,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5066 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5067 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 200 276 48 65 138 266), lower := (rows 35 67 164 200 276 48 65 128 256), losses := [] }

theorem u5067 : Upper (D 7) (R 7) [34,65,160,192,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5067 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5068 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 200 276 48 66 137 265), lower := (rows 35 67 164 200 276 48 66 128 256), losses := [] }

theorem u5068 : Upper (D 7) (R 7) [34,65,160,192,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5068 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5069 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 164 200 276 48 72 131 259), lower := (rows 35 67 164 200 276 48 72 128 256), losses := [] }

theorem u5069 : Upper (D 7) (R 7) [34,65,160,192,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5069 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5070 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(2,5),(4,1)], upper := (rows 35 70 13 26 145 288 96 192 448), lower := (rows 35 70 13 26 145 288 96 128 256), losses := [{ target := 5, region := (rows 1 2 21 9 17 0 64 194 322), good := (rows 415 454 29 414 157 256 448 128 256) }] }

theorem u5070 : Upper (D 7) (R 7) [34,68,9,18,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5070 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5071 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 78, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 13 26 145 288 192 224 352), lower := (rows 35 70 13 26 145 288 192 128 256), losses := [] }

theorem u5071 : Upper (D 7) (R 7) [34,68,9,18,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5071 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5072 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 13 26 176 288 65 192 448), lower := (rows 35 70 13 26 176 288 65 128 256), losses := [] }

theorem u5072 : Upper (D 7) (R 7) [34,68,9,18,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5072 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5073 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 289, targets := 128 },{ cop := 2, region := 194, targets := 32 }], pairs := [(0,7),(1,5),(4,1)], upper := (rows 35 70 13 26 176 288 192 193 321), lower := (rows 35 70 13 26 176 288 192 128 256), losses := [] }

theorem u5073 : Upper (D 7) (R 7) [34,68,9,18,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5073 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5074 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 464, targets := 2 },{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,1)], upper := (rows 35 70 13 26 273 160 96 192 448), lower := (rows 35 70 13 26 273 160 96 128 256), losses := [{ target := 5, region := (rows 1 2 21 9 17 0 64 194 322), good := (rows 415 454 29 414 285 128 448 128 256) }] }

theorem u5074 : Upper (D 7) (R 7) [34,68,9,18,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5075 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 464, targets := 2 },{ cop := 2, region := 226, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,1)], upper := (rows 35 70 13 26 273 160 192 224 352), lower := (rows 35 70 13 26 273 160 192 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 224 0 128 256), good := (rows 35 39 13 31 273 160 160 160 256) }] }

theorem u5075 : Upper (D 7) (R 7) [34,68,9,18,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5076 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 26 304 160 65 192 448), lower := (rows 35 70 13 26 304 160 65 128 256), losses := [] }

theorem u5076 : Upper (D 7) (R 7) [34,68,9,18,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5077 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 464, targets := 2 },{ cop := 2, region := 194, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,1)], upper := (rows 35 70 13 26 304 160 192 193 321), lower := (rows 35 70 13 26 304 160 192 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 224 0 128 256), good := (rows 35 39 13 31 304 160 160 160 256) }] }

theorem u5077 : Upper (D 7) (R 7) [34,68,9,18,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5078 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 160 }], pairs := [(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 70 13 26 336 160 65 160 416), lower := (rows 35 70 13 26 336 160 65 128 256), losses := [] }

theorem u5078 : Upper (D 7) (R 7) [34,68,9,18,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5079 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(1,0),(2,6),(4,1)], upper := (rows 35 70 13 26 336 160 96 129 385), lower := (rows 35 70 13 26 336 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 160 225 128 256), good := (rows 98 70 78 26 336 224 96 224 256) }] }

theorem u5079 : Upper (D 7) (R 7) [34,68,9,18,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5080 : Route 9 := (fun mask => (mask,id))

def c5080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5080 : Upper (D 7) (R 7) [34,68,9,18,320,128,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18,320,128,128] 13 (by decide) (choices 1) [1,32] r5080 c5080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u380
  · exact u381

def b5081 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 1, region := 440, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 56 274 160 65 192 448), lower := (rows 35 70 13 56 274 160 65 128 256), losses := [] }

theorem u5081 : Upper (D 7) (R 7) [34,68,9,48,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5082 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(0,6),(1,5),(3,1),(4,5)], upper := (rows 35 70 13 56 274 160 192 193 321), lower := (rows 35 70 13 56 274 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 231 231 133 261), good := (rows 481 484 493 120 376 224 224 224 256) },{ target := 6, region := (rows 3 2 4 8 16 224 0 128 256), good := (rows 35 39 13 56 275 160 160 160 256) }] }

theorem u5082 : Upper (D 7) (R 7) [34,68,9,48,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5083 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 1, region := 440, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 56 336 160 65 130 386), lower := (rows 35 70 13 56 336 160 65 128 256), losses := [] }

theorem u5083 : Upper (D 7) (R 7) [34,68,9,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5084 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 2, region := 66, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 35 70 13 56 336 160 66 129 385), lower := (rows 35 70 13 56 336 160 66 128 256), losses := [] }

theorem u5084 : Upper (D 7) (R 7) [34,68,9,48,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5085 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(3,0),(4,5)], upper := (rows 35 70 13 56 336 160 192 131 259), lower := (rows 35 70 13 56 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 98 102 12 120 376 224 224 224 256) }] }

theorem u5085 : Upper (D 7) (R 7) [34,68,9,48,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5086 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(4,0),(4,6)], upper := (rows 35 70 13 88 274 160 65 160 416), lower := (rows 35 70 13 88 274 160 65 128 256), losses := [] }

theorem u5086 : Upper (D 7) (R 7) [34,68,9,80,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5087 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(1,0),(4,5),(4,6)], upper := (rows 35 70 13 88 274 160 96 129 385), lower := (rows 35 70 13 88 274 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 160 225 128 256), good := (rows 98 70 78 88 274 224 96 224 256) }] }

theorem u5087 : Upper (D 7) (R 7) [34,68,9,80,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5088 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(0,6),(3,1),(4,6),(4,7)], upper := (rows 35 70 13 88 274 160 192 161 289), lower := (rows 35 70 13 88 274 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 231 231 133 261), good := (rows 481 484 493 120 376 224 224 224 256) }] }

theorem u5088 : Upper (D 7) (R 7) [34,68,9,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5089 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 88 304 160 65 130 386), lower := (rows 35 70 13 88 304 160 65 128 256), losses := [] }

theorem u5089 : Upper (D 7) (R 7) [34,68,9,80,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5090 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 88 304 160 66 129 385), lower := (rows 35 70 13 88 304 160 66 128 256), losses := [] }

theorem u5090 : Upper (D 7) (R 7) [34,68,9,80,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5091 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 272, targets := 128 },{ cop := 2, region := 194, targets := 32 }], pairs := [(0,6),(1,5),(4,6),(4,7)], upper := (rows 35 70 13 88 304 160 192 131 259), lower := (rows 35 70 13 88 304 160 192 128 256), losses := [] }

theorem u5091 : Upper (D 7) (R 7) [34,68,9,80,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5092 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(4,0),(4,6)], upper := (rows 35 70 13 88 400 160 65 162 290), lower := (rows 35 70 13 88 400 160 65 128 256), losses := [] }

theorem u5092 : Upper (D 7) (R 7) [34,68,9,80,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5093 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 400, targets := 2 }], pairs := [(1,0),(1,5),(1,7),(4,1)], upper := (rows 35 70 13 88 400 160 66 161 289), lower := (rows 35 70 13 88 400 160 66 128 256), losses := [] }

theorem u5093 : Upper (D 7) (R 7) [34,68,9,80,384,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5094 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 104, targets := 3 }], pairs := [(0,6),(3,0),(3,1),(4,6)], upper := (rows 35 70 13 88 400 160 96 131 259), lower := (rows 35 70 13 88 400 160 96 128 256), losses := [] }

theorem u5094 : Upper (D 7) (R 7) [34,68,9,80,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5095 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 82, targets := 160 }], pairs := [(1,5),(1,7)], upper := (rows 35 70 13 138 81 288 80 160 416), lower := (rows 35 70 13 138 81 288 80 128 256), losses := [] }

theorem u5095 : Upper (D 7) (R 7) [34,68,9,130,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5095 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5096 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 142, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 13 138 81 288 96 144 400), lower := (rows 35 70 13 138 81 288 96 128 256), losses := [] }

theorem u5096 : Upper (D 7) (R 7) [34,68,9,130,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5096 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5097 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 305, targets := 128 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,7),(4,1),(4,7)], upper := (rows 35 70 13 138 81 288 192 176 304), lower := (rows 35 70 13 138 81 288 192 128 256), losses := [] }

theorem u5097 : Upper (D 7) (R 7) [34,68,9,130,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5097 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5098 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 70 13 138 112 288 65 144 400), lower := (rows 35 70 13 138 112 288 65 128 256), losses := [] }

theorem u5098 : Upper (D 7) (R 7) [34,68,9,130,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5098 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5099 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 13 138 112 288 80 129 385), lower := (rows 35 70 13 138 112 288 80 128 256), losses := [] }

theorem u5099 : Upper (D 7) (R 7) [34,68,9,130,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5099 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5099
end Delivery.IrregularNine14.P07
