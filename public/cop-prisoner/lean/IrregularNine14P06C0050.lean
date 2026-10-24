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

def b3000 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 404, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 388 73 84 34 96 145 273), lower := (rows 11 38 388 73 84 34 96 128 256), losses := [] }

theorem u3000 : Upper (D 6) (R 6) [10,36,384,65,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3001 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 388 88 21 96 65 162 290), lower := (rows 11 38 388 88 21 96 65 128 256), losses := [] }

theorem u3001 : Upper (D 6) (R 6) [10,36,384,80,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3002 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 388 88 21 96 66 161 289), lower := (rows 11 38 388 88 21 96 66 128 256), losses := [] }

theorem u3002 : Upper (D 6) (R 6) [10,36,384,80,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3003 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 388 88 21 96 96 131 259), lower := (rows 11 38 388 88 21 96 96 128 256), losses := [] }

theorem u3003 : Upper (D 6) (R 6) [10,36,384,80,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3004 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 388 104 84 33 65 146 274), lower := (rows 11 38 388 104 84 33 65 128 256), losses := [] }

theorem u3004 : Upper (D 6) (R 6) [10,36,384,96,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3005 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 388 104 84 33 66 145 273), lower := (rows 11 38 388 104 84 33 66 128 256), losses := [] }

theorem u3005 : Upper (D 6) (R 6) [10,36,384,96,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3006 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 388 104 84 33 80 131 259), lower := (rows 11 38 388 104 84 33 80 128 256), losses := [] }

theorem u3006 : Upper (D 6) (R 6) [10,36,384,96,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3006 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3007 : PairBound 9 := { available := 68, camps := [], pairs := [(1,0),(3,0)], upper := (rows 11 50 37 76 145 288 66 196 324), lower := (rows 11 50 37 76 145 288 66 128 256), losses := [{ target := 0, region := (rows 0 18 4 12 16 301 83 140 268), good := (rows 490 114 492 492 242 288 66 128 288) }] }

theorem u3007 : Upper (D 6) (R 6) [10,48,33,68,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3007 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3008 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 50 37 76 145 288 68 194 322), lower := (rows 11 50 37 76 145 288 68 128 256), losses := [] }

theorem u3008 : Upper (D 6) (R 6) [10,48,33,68,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3008 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3009 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 11 50 37 76 208 288 65 134 262), lower := (rows 11 50 37 76 208 288 65 128 256), losses := [] }

theorem u3009 : Upper (D 6) (R 6) [10,48,33,68,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3009 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3010 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 50 37 76 208 288 66 133 261), lower := (rows 11 50 37 76 208 288 66 128 256), losses := [] }

theorem u3010 : Upper (D 6) (R 6) [10,48,33,68,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3010 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3011 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 50 37 76 208 288 68 131 259), lower := (rows 11 50 37 76 208 288 68 128 256), losses := [] }

theorem u3011 : Upper (D 6) (R 6) [10,48,33,68,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3011 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3012 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 338, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 37 137 276 96 66 196 324), lower := (rows 11 50 37 137 276 96 66 128 256), losses := [] }

theorem u3012 : Upper (D 6) (R 6) [10,48,33,129,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3013 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 338, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 11 50 37 137 276 96 68 194 322), lower := (rows 11 50 37 137 276 96 68 128 256), losses := [] }

theorem u3013 : Upper (D 6) (R 6) [10,48,33,129,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3014 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 11 50 37 140 81 288 66 196 324), lower := (rows 11 50 37 140 81 288 66 128 256), losses := [] }

theorem u3014 : Upper (D 6) (R 6) [10,48,33,132,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3014 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3015 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 80, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 11 50 37 140 81 288 68 194 322), lower := (rows 11 50 37 140 81 288 68 128 256), losses := [] }

theorem u3015 : Upper (D 6) (R 6) [10,48,33,132,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3015 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3016 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 11 50 37 140 273 96 66 196 324), lower := (rows 11 50 37 140 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 18 4 12 16 119 83 132 260), good := (rows 106 114 492 428 370 96 98 128 256) }] }

theorem u3016 : Upper (D 6) (R 6) [10,48,33,132,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3017 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 50 37 140 273 96 68 194 322), lower := (rows 11 50 37 140 273 96 68 128 256), losses := [{ target := 0, region := (rows 0 18 4 12 16 109 76 129 257), good := (rows 490 50 492 236 434 96 108 128 256) }] }

theorem u3017 : Upper (D 6) (R 6) [10,48,33,132,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3018 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,6),(2,1),(2,6)], upper := (rows 11 50 37 200 336 36 65 134 262), lower := (rows 11 50 37 200 336 36 65 128 256), losses := [{ target := 6, region := (rows 1 18 69 8 16 125 0 145 273), good := (rows 431 434 421 172 438 36 421 128 256) }] }

theorem u3018 : Upper (D 6) (R 6) [10,48,33,192,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3019 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(3,5)], upper := (rows 11 50 37 200 336 36 66 133 261), lower := (rows 11 50 37 200 336 36 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 20 0 67 132 260), good := (rows 75 82 477 200 336 412 66 128 256) }] }

theorem u3019 : Upper (D 6) (R 6) [10,48,33,192,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3020 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 50 37 200 336 36 68 131 259), lower := (rows 11 50 37 200 336 36 68 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 100 100 128 256), good := (rows 10 114 100 232 370 100 100 128 256) }] }

theorem u3020 : Upper (D 6) (R 6) [10,48,33,192,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3021 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 306, targets := 1 },{ cop := 2, region := 168, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 50 69 137 336 36 66 164 292), lower := (rows 11 50 69 137 336 36 66 128 256), losses := [] }

theorem u3021 : Upper (D 6) (R 6) [10,48,65,129,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3022 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 137, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 69 137 336 36 68 162 290), lower := (rows 11 50 69 137 336 36 68 128 256), losses := [] }

theorem u3022 : Upper (D 6) (R 6) [10,48,65,129,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3023 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 306, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 11 50 69 137 336 36 96 134 262), lower := (rows 11 50 69 137 336 36 96 128 256), losses := [] }

theorem u3023 : Upper (D 6) (R 6) [10,48,65,129,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3024 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 440, targets := 2 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 50 69 140 273 36 66 224 352), lower := (rows 11 50 69 140 273 36 66 128 256), losses := [] }

theorem u3024 : Upper (D 6) (R 6) [10,48,65,132,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3025 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(1,2),(2,1),(3,0)], upper := (rows 11 50 69 140 273 36 96 194 322), lower := (rows 11 50 69 140 273 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 44 111 131 259), good := (rows 490 498 492 236 464 108 96 128 256) },{ target := 2, region := (rows 1 34 0 8 21 32 98 227 355), good := (rows 475 498 465 152 401 498 482 128 256) }] }

theorem u3025 : Upper (D 6) (R 6) [10,48,65,132,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3026 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 2 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 11 50 69 140 273 96 66 164 292), lower := (rows 11 50 69 140 273 96 66 128 256), losses := [] }

theorem u3026 : Upper (D 6) (R 6) [10,48,65,132,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3027 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 306, targets := 4 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 11 50 69 140 273 96 68 162 290), lower := (rows 11 50 69 140 273 96 68 128 256), losses := [] }

theorem u3027 : Upper (D 6) (R 6) [10,48,65,132,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3028 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 98, targets := 5 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(1,2),(2,1)], upper := (rows 11 50 69 140 273 96 96 134 262), lower := (rows 11 50 69 140 273 96 96 128 256), losses := [] }

theorem u3028 : Upper (D 6) (R 6) [10,48,65,132,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3029 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 306, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 50 69 140 274 33 68 224 352), lower := (rows 11 50 69 140 274 33 68 128 256), losses := [] }

theorem u3029 : Upper (D 6) (R 6) [10,48,65,132,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3030 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 136, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 50 69 140 274 33 96 196 324), lower := (rows 11 50 69 140 274 33 96 128 256), losses := [] }

theorem u3030 : Upper (D 6) (R 6) [10,48,65,132,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3031 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 69 140 274 36 65 224 352), lower := (rows 11 50 69 140 274 36 65 128 256), losses := [] }

theorem u3031 : Upper (D 6) (R 6) [10,48,65,132,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3032 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 136, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 11 50 69 140 274 36 96 193 321), lower := (rows 11 50 69 140 274 36 96 128 256), losses := [] }

theorem u3032 : Upper (D 6) (R 6) [10,48,65,132,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3033 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 69 140 274 96 65 164 292), lower := (rows 11 50 69 140 274 96 65 128 256), losses := [] }

theorem u3033 : Upper (D 6) (R 6) [10,48,65,132,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3034 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 306, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 50 69 140 274 96 68 161 289), lower := (rows 11 50 69 140 274 96 68 128 256), losses := [] }

theorem u3034 : Upper (D 6) (R 6) [10,48,65,132,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3035 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 114, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 69 140 274 96 96 133 261), lower := (rows 11 50 69 140 274 96 96 128 256), losses := [] }

theorem u3035 : Upper (D 6) (R 6) [10,48,65,132,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3036 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 440, targets := 2 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 50 69 140 276 33 66 224 352), lower := (rows 11 50 69 140 276 33 66 128 256), losses := [] }

theorem u3036 : Upper (D 6) (R 6) [10,48,65,132,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3037 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 50 69 140 276 33 96 194 322), lower := (rows 11 50 69 140 276 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 32 98 131 259), good := (rows 458 498 476 156 284 480 96 128 256) }] }

theorem u3037 : Upper (D 6) (R 6) [10,48,65,132,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3038 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 69 140 276 96 65 162 290), lower := (rows 11 50 69 140 276 96 65 128 256), losses := [] }

theorem u3038 : Upper (D 6) (R 6) [10,48,65,132,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3039 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 440, targets := 2 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 11 50 69 140 276 96 66 161 289), lower := (rows 11 50 69 140 276 96 66 128 256), losses := [] }

theorem u3039 : Upper (D 6) (R 6) [10,48,65,132,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3040 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 98, targets := 5 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(1,2),(2,1)], upper := (rows 11 50 69 140 276 96 96 131 259), lower := (rows 11 50 69 140 276 96 96 128 256), losses := [] }

theorem u3040 : Upper (D 6) (R 6) [10,48,65,132,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3041 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 2 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 50 69 140 336 33 66 164 292), lower := (rows 11 50 69 140 336 33 66 128 256), losses := [] }

theorem u3041 : Upper (D 6) (R 6) [10,48,65,132,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3042 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 306, targets := 4 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 11 50 69 140 336 33 68 162 290), lower := (rows 11 50 69 140 336 33 68 128 256), losses := [] }

theorem u3042 : Upper (D 6) (R 6) [10,48,65,132,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3043 : Route 9 := (fun mask => (mask,id))

def c3043 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3043 : Upper (D 6) (R 6) [10,48,65,132,320,1,32] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,320,1,32] 13 (by decide) (choices 1) [2,4] r3043 c3043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u214
  · exact u215

def b3044 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 69 140 336 36 65 162 290), lower := (rows 11 50 69 140 336 36 65 128 256), losses := [] }

theorem u3044 : Upper (D 6) (R 6) [10,48,65,132,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3045 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 440, targets := 2 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 50 69 140 336 36 66 161 289), lower := (rows 11 50 69 140 336 36 66 128 256), losses := [] }

theorem u3045 : Upper (D 6) (R 6) [10,48,65,132,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3046 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 11 50 69 140 336 36 96 131 259), lower := (rows 11 50 69 140 336 36 96 128 256), losses := [{ target := 2, region := (rows 1 98 0 8 53 32 98 133 261), good := (rows 475 114 467 408 338 498 114 128 256) }] }

theorem u3046 : Upper (D 6) (R 6) [10,48,65,132,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3047 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 168, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 69 168 273 36 66 196 324), lower := (rows 11 50 69 168 273 36 66 128 256), losses := [] }

theorem u3047 : Upper (D 6) (R 6) [10,48,65,160,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3048 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 50 69 168 273 36 68 194 322), lower := (rows 11 50 69 168 273 36 68 128 256), losses := [] }

theorem u3048 : Upper (D 6) (R 6) [10,48,65,160,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3049 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 168, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 69 168 273 96 66 132 260), lower := (rows 11 50 69 168 273 96 66 128 256), losses := [] }

theorem u3049 : Upper (D 6) (R 6) [10,48,65,160,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3050 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 50 69 168 273 96 68 134 262), lower := (rows 11 50 69 168 273 96 68 128 256), losses := [] }

theorem u3050 : Upper (D 6) (R 6) [10,48,65,160,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3051 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 168, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 69 168 336 33 66 132 260), lower := (rows 11 50 69 168 336 33 66 128 256), losses := [] }

theorem u3051 : Upper (D 6) (R 6) [10,48,65,160,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3052 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 50 69 168 336 33 68 134 262), lower := (rows 11 50 69 168 336 33 68 128 256), losses := [] }

theorem u3052 : Upper (D 6) (R 6) [10,48,65,160,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3053 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 69 168 336 36 65 134 262), lower := (rows 11 50 69 168 336 36 65 128 256), losses := [] }

theorem u3053 : Upper (D 6) (R 6) [10,48,65,160,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3054 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 168, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 69 168 336 36 66 133 261), lower := (rows 11 50 69 168 336 36 66 128 256), losses := [] }

theorem u3054 : Upper (D 6) (R 6) [10,48,65,160,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3055 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 137, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 69 168 336 36 68 131 259), lower := (rows 11 50 69 168 336 36 68 128 256), losses := [] }

theorem u3055 : Upper (D 6) (R 6) [10,48,65,160,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3056 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 2 },{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 11 50 69 200 273 36 66 164 292), lower := (rows 11 50 69 200 273 36 66 128 256), losses := [] }

theorem u3056 : Upper (D 6) (R 6) [10,48,65,192,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3057 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 306, targets := 64 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 50 69 200 273 36 68 162 290), lower := (rows 11 50 69 200 273 36 68 128 256), losses := [] }

theorem u3057 : Upper (D 6) (R 6) [10,48,65,192,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3058 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 306, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 50 69 200 273 36 96 134 262), lower := (rows 11 50 69 200 273 36 96 128 256), losses := [] }

theorem u3058 : Upper (D 6) (R 6) [10,48,65,192,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3059 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 50 70 137 273 36 68 224 352), lower := (rows 11 50 70 137 273 36 68 128 256), losses := [] }

theorem u3059 : Upper (D 6) (R 6) [10,48,66,129,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3059
end Delivery.IrregularNine14.P06
