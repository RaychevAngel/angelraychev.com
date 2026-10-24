import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0003

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3060 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 50 70 137 273 36 96 196 324), lower := (rows 11 50 70 137 273 36 96 128 256), losses := [] }

theorem u3060 : Upper (D 6) (R 6) [10,48,66,129,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3061 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 50 70 137 273 96 68 164 292), lower := (rows 11 50 70 137 273 96 68 128 256), losses := [] }

theorem u3061 : Upper (D 6) (R 6) [10,48,66,129,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3062 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 137, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 50 70 137 273 96 96 132 260), lower := (rows 11 50 70 137 273 96 96 128 256), losses := [] }

theorem u3062 : Upper (D 6) (R 6) [10,48,66,129,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3063 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 278, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 70 137 276 96 65 164 292), lower := (rows 11 50 70 137 276 96 65 128 256), losses := [] }

theorem u3063 : Upper (D 6) (R 6) [10,48,66,129,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3064 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 137, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 70 137 276 96 68 161 289), lower := (rows 11 50 70 137 276 96 68 128 256), losses := [] }

theorem u3064 : Upper (D 6) (R 6) [10,48,66,129,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3065 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 50 70 137 276 96 96 133 261), lower := (rows 11 50 70 137 276 96 96 128 256), losses := [] }

theorem u3065 : Upper (D 6) (R 6) [10,48,66,129,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3066 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 168, targets := 3 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,0),(3,1)], upper := (rows 11 50 70 140 273 36 65 224 352), lower := (rows 11 50 70 140 273 36 65 128 256), losses := [] }

theorem u3066 : Upper (D 6) (R 6) [10,48,66,132,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3067 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 50 70 140 273 36 96 193 321), lower := (rows 11 50 70 140 273 36 96 128 256), losses := [] }

theorem u3067 : Upper (D 6) (R 6) [10,48,66,132,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3068 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 168, targets := 3 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,0),(3,1)], upper := (rows 11 50 70 140 273 96 65 164 292), lower := (rows 11 50 70 140 273 96 65 128 256), losses := [] }

theorem u3068 : Upper (D 6) (R 6) [10,48,66,132,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3069 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 50 70 140 273 96 68 161 289), lower := (rows 11 50 70 140 273 96 68 128 256), losses := [] }

theorem u3069 : Upper (D 6) (R 6) [10,48,66,132,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3070 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 50 70 140 273 96 96 133 261), lower := (rows 11 50 70 140 273 96 96 128 256), losses := [] }

theorem u3070 : Upper (D 6) (R 6) [10,48,66,132,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3071 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 50 70 140 276 33 65 224 352), lower := (rows 11 50 70 140 276 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 28 97 97 231 359), good := (rows 505 504 508 412 412 481 481 128 256) }] }

theorem u3071 : Upper (D 6) (R 6) [10,48,66,132,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3072 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 50 70 140 276 33 96 193 321), lower := (rows 11 50 70 140 276 33 96 128 256), losses := [] }

theorem u3072 : Upper (D 6) (R 6) [10,48,66,132,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3073 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,5),(3,1)], upper := (rows 11 50 70 140 276 96 65 161 289), lower := (rows 11 50 70 140 276 96 65 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 100 64 128 256), good := (rows 10 50 102 172 310 96 96 128 256) },{ target := 1, region := (rows 1 0 4 12 20 101 65 193 321), good := (rows 489 48 508 188 316 480 481 128 256) }] }

theorem u3073 : Upper (D 6) (R 6) [10,48,66,132,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3074 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 137, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 50 70 140 276 96 96 129 257), lower := (rows 11 50 70 140 276 96 96 128 256), losses := [] }

theorem u3074 : Upper (D 6) (R 6) [10,48,66,132,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3075 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 169, targets := 64 },{ cop := 0, region := 68, targets := 32 }], pairs := [(0,6),(2,5),(3,6)], upper := (rows 11 50 70 140 336 33 65 164 292), lower := (rows 11 50 70 140 336 33 65 128 256), losses := [] }

theorem u3075 : Upper (D 6) (R 6) [10,48,66,132,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3076 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 33 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,6),(2,0),(2,5)], upper := (rows 11 50 70 140 336 33 68 161 289), lower := (rows 11 50 70 140 336 33 68 128 256), losses := [] }

theorem u3076 : Upper (D 6) (R 6) [10,48,66,132,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3077 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 50 70 140 336 33 96 133 261), lower := (rows 11 50 70 140 336 33 96 128 256), losses := [] }

theorem u3077 : Upper (D 6) (R 6) [10,48,66,132,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3078 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 168, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 50 70 168 273 36 65 196 324), lower := (rows 11 50 70 168 273 36 65 128 256), losses := [] }

theorem u3078 : Upper (D 6) (R 6) [10,48,66,160,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3079 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 102, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 50 70 168 273 36 68 193 321), lower := (rows 11 50 70 168 273 36 68 128 256), losses := [] }

theorem u3079 : Upper (D 6) (R 6) [10,48,66,160,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3080 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 168, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 50 70 168 273 96 65 132 260), lower := (rows 11 50 70 168 273 96 65 128 256), losses := [] }

theorem u3080 : Upper (D 6) (R 6) [10,48,66,160,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3081 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 102, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 50 70 168 273 96 68 133 261), lower := (rows 11 50 70 168 273 96 68 128 256), losses := [] }

theorem u3081 : Upper (D 6) (R 6) [10,48,66,160,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3082 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 70 168 276 33 65 196 324), lower := (rows 11 50 70 168 276 33 65 128 256), losses := [] }

theorem u3082 : Upper (D 6) (R 6) [10,48,66,160,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3083 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 169, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 70 168 276 33 68 193 321), lower := (rows 11 50 70 168 276 33 68 128 256), losses := [] }

theorem u3083 : Upper (D 6) (R 6) [10,48,66,160,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3084 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 168, targets := 3 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,0),(3,1)], upper := (rows 11 50 70 200 273 36 65 164 292), lower := (rows 11 50 70 200 273 36 65 128 256), losses := [] }

theorem u3084 : Upper (D 6) (R 6) [10,48,66,192,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3085 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 50 70 200 273 36 68 161 289), lower := (rows 11 50 70 200 273 36 68 128 256), losses := [] }

theorem u3085 : Upper (D 6) (R 6) [10,48,66,192,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3086 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 50 70 200 273 36 96 133 261), lower := (rows 11 50 70 200 273 36 96 128 256), losses := [] }

theorem u3086 : Upper (D 6) (R 6) [10,48,66,192,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3087 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 50 70 200 276 33 65 164 292), lower := (rows 11 50 70 200 276 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 97 97 132 260), good := (rows 105 112 508 232 412 97 97 128 256) }] }

theorem u3087 : Upper (D 6) (R 6) [10,48,66,192,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3088 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 33 },{ cop := 2, region := 169, targets := 4 }], pairs := [(0,2),(2,0),(2,5)], upper := (rows 11 50 70 200 276 33 68 161 289), lower := (rows 11 50 70 200 276 33 68 128 256), losses := [] }

theorem u3088 : Upper (D 6) (R 6) [10,48,66,192,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3089 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 50 70 200 276 33 96 133 261), lower := (rows 11 50 70 200 276 33 96 128 256), losses := [] }

theorem u3089 : Upper (D 6) (R 6) [10,48,66,192,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3090 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 50 100 13 148 288 65 194 322), lower := (rows 11 50 100 13 148 288 65 128 256), losses := [] }

theorem u3090 : Upper (D 6) (R 6) [10,48,96,5,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3090 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3091 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(4,5)], upper := (rows 11 50 100 13 148 288 66 193 321), lower := (rows 11 50 100 13 148 288 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 24 0 67 137 265), good := (rows 475 82 68 477 148 256 66 128 256) }] }

theorem u3091 : Upper (D 6) (R 6) [10,48,96,5,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3091 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3092 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 50 100 13 208 288 65 134 262), lower := (rows 11 50 100 13 208 288 65 128 256), losses := [] }

theorem u3092 : Upper (D 6) (R 6) [10,48,96,5,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3092 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3093 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(4,5)], upper := (rows 11 50 100 13 208 288 66 133 261), lower := (rows 11 50 100 13 208 288 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 25 0 67 136 264), good := (rows 475 82 68 477 208 256 66 128 256) }] }

theorem u3093 : Upper (D 6) (R 6) [10,48,96,5,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3093 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3094 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 50 100 13 208 288 68 131 259), lower := (rows 11 50 100 13 208 288 68 128 256), losses := [] }

theorem u3094 : Upper (D 6) (R 6) [10,48,96,5,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3094 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3095 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 50 100 73 148 288 65 134 262), lower := (rows 11 50 100 73 148 288 65 128 256), losses := [] }

theorem u3095 : Upper (D 6) (R 6) [10,48,96,65,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3095 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3096 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 50 100 73 148 288 66 133 261), lower := (rows 11 50 100 73 148 288 66 128 256), losses := [] }

theorem u3096 : Upper (D 6) (R 6) [10,48,96,65,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3096 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3097 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 50 100 73 148 288 68 131 259), lower := (rows 11 50 100 73 148 288 68 128 256), losses := [] }

theorem u3097 : Upper (D 6) (R 6) [10,48,96,65,132,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3097 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3098 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 100 73 400 36 65 134 262), lower := (rows 11 50 100 73 400 36 65 128 256), losses := [] }

theorem u3098 : Upper (D 6) (R 6) [10,48,96,65,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3099 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 100 73 400 36 66 133 261), lower := (rows 11 50 100 73 400 36 66 128 256), losses := [] }

theorem u3099 : Upper (D 6) (R 6) [10,48,96,65,384,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3100 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 100 73 400 36 68 131 259), lower := (rows 11 50 100 73 400 36 68 128 256), losses := [] }

theorem u3100 : Upper (D 6) (R 6) [10,48,96,65,384,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3101 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 50 100 140 81 288 65 134 262), lower := (rows 11 50 100 140 81 288 65 128 256), losses := [] }

theorem u3101 : Upper (D 6) (R 6) [10,48,96,132,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3101 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3102 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 11 50 100 140 81 288 66 133 261), lower := (rows 11 50 100 140 81 288 66 128 256), losses := [] }

theorem u3102 : Upper (D 6) (R 6) [10,48,96,132,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3102 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3103 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 290, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 11 50 100 140 81 288 68 131 259), lower := (rows 11 50 100 140 81 288 68 128 256), losses := [] }

theorem u3103 : Upper (D 6) (R 6) [10,48,96,132,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3103 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3104 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 100 140 274 33 65 196 324), lower := (rows 11 50 100 140 274 33 65 128 256), losses := [] }

theorem u3104 : Upper (D 6) (R 6) [10,48,96,132,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3105 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 50 100 140 274 33 68 193 321), lower := (rows 11 50 100 140 274 33 68 128 256), losses := [] }

theorem u3105 : Upper (D 6) (R 6) [10,48,96,132,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3106 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 100 140 276 33 65 194 322), lower := (rows 11 50 100 140 276 33 65 128 256), losses := [] }

theorem u3106 : Upper (D 6) (R 6) [10,48,96,132,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3107 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 11 50 100 140 276 33 66 193 321), lower := (rows 11 50 100 140 276 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 20 0 67 161 289), good := (rows 459 466 476 156 284 449 66 128 256) }] }

theorem u3107 : Upper (D 6) (R 6) [10,48,96,132,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3108 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 100 140 336 33 65 134 262), lower := (rows 11 50 100 140 336 33 65 128 256), losses := [] }

theorem u3108 : Upper (D 6) (R 6) [10,48,96,132,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3109 : Route 9 := (fun mask => (mask,id))

def c3109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3109 : Upper (D 6) (R 6) [10,48,96,132,320,1,2] 13 := by
  apply FastRouting.sound _ _ [10,48,96,132,320,1,2] 13 (by decide) (choices 1) [1,4] r3109 c3109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u216
  · exact u217

def b3110 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(4,5)], upper := (rows 11 50 100 140 336 33 68 131 259), lower := (rows 11 50 100 140 336 33 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 76 129 257), good := (rows 475 18 68 204 336 401 68 128 256) }] }

theorem u3110 : Upper (D 6) (R 6) [10,48,96,132,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3111 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 290, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 50 100 200 21 288 65 134 262), lower := (rows 11 50 100 200 21 288 65 128 256), losses := [] }

theorem u3111 : Upper (D 6) (R 6) [10,48,96,192,5,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3111 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3112 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 68, targets := 1 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,6),(2,0)], upper := (rows 11 50 100 200 21 288 66 133 261), lower := (rows 11 50 100 200 21 288 66 128 256), losses := [] }

theorem u3112 : Upper (D 6) (R 6) [10,48,96,192,5,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3112 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3113 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 290, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 11 50 100 200 21 288 68 131 259), lower := (rows 11 50 100 200 21 288 68 128 256), losses := [] }

theorem u3113 : Upper (D 6) (R 6) [10,48,96,192,5,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3113 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3114 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 100 200 274 33 65 132 260), lower := (rows 11 50 100 200 274 33 65 128 256), losses := [] }

theorem u3114 : Upper (D 6) (R 6) [10,48,96,192,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3115 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 50 100 200 274 33 68 133 261), lower := (rows 11 50 100 200 274 33 68 128 256), losses := [] }

theorem u3115 : Upper (D 6) (R 6) [10,48,96,192,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3116 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 100 200 276 33 65 134 262), lower := (rows 11 50 100 200 276 33 65 128 256), losses := [] }

theorem u3116 : Upper (D 6) (R 6) [10,48,96,192,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3117 : Route 9 := (fun mask => (mask,id))

def c3117 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3117 : Upper (D 6) (R 6) [10,48,96,192,260,1,2] 13 := by
  apply FastRouting.sound _ _ [10,48,96,192,260,1,2] 13 (by decide) (choices 1) [1,4] r3117 c3117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u218
  · exact u219

def b3118 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(0,5),(2,0),(2,1)], upper := (rows 11 50 100 200 276 33 68 131 259), lower := (rows 11 50 100 200 276 33 68 128 256), losses := [{ target := 5, region := (rows 3 2 4 10 16 0 84 131 259), good := (rows 395 475 68 200 340 385 68 128 256) }] }

theorem u3118 : Upper (D 6) (R 6) [10,48,96,192,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3119 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 50 133 44 273 96 66 196 324), lower := (rows 11 50 133 44 273 96 66 128 256), losses := [] }

theorem u3119 : Upper (D 6) (R 6) [10,48,129,36,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3119
end Delivery.IrregularNine14.P06
