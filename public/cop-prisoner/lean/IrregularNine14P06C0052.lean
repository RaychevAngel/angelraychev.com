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

def b3120 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 104, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 50 133 44 273 96 68 194 322), lower := (rows 11 50 133 44 273 96 68 128 256), losses := [] }

theorem u3120 : Upper (D 6) (R 6) [10,48,129,36,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3121 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 133 73 276 96 66 164 292), lower := (rows 11 50 133 73 276 96 66 128 256), losses := [] }

theorem u3121 : Upper (D 6) (R 6) [10,48,129,65,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3122 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 2, region := 72, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 50 133 73 276 96 68 162 290), lower := (rows 11 50 133 73 276 96 68 128 256), losses := [] }

theorem u3122 : Upper (D 6) (R 6) [10,48,129,65,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3123 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 133 73 276 96 96 134 262), lower := (rows 11 50 133 73 276 96 96 128 256), losses := [] }

theorem u3123 : Upper (D 6) (R 6) [10,48,129,65,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3124 : PairBound 9 := { available := 96, camps := [], pairs := [(2,1),(3,0),(4,1)], upper := (rows 11 50 133 76 273 36 66 224 352), lower := (rows 11 50 133 76 273 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 44 67 143 271), good := (rows 490 498 492 492 464 428 450 128 256) },{ target := 1, region := (rows 1 0 5 8 17 61 64 136 264), good := (rows 445 48 181 492 309 36 64 128 256) }] }

theorem u3124 : Upper (D 6) (R 6) [10,48,129,68,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3125 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 104, targets := 3 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 50 133 76 273 36 96 194 322), lower := (rows 11 50 133 76 273 36 96 128 256), losses := [{ target := 2, region := (rows 1 34 0 8 21 32 98 227 355), good := (rows 475 498 401 472 401 498 482 128 256) }] }

theorem u3125 : Upper (D 6) (R 6) [10,48,129,68,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3126 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 11 50 133 76 273 96 66 164 292), lower := (rows 11 50 133 76 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 18 4 12 16 127 83 140 268), good := (rows 490 114 492 492 370 96 98 128 256) }] }

theorem u3126 : Upper (D 6) (R 6) [10,48,129,68,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3127 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 133 76 273 96 68 162 290), lower := (rows 11 50 133 76 273 96 68 128 256), losses := [] }

theorem u3127 : Upper (D 6) (R 6) [10,48,129,68,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3128 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 133 76 273 96 96 134 262), lower := (rows 11 50 133 76 273 96 96 128 256), losses := [] }

theorem u3128 : Upper (D 6) (R 6) [10,48,129,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3129 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 133 76 274 33 68 224 352), lower := (rows 11 50 133 76 274 33 68 128 256), losses := [] }

theorem u3129 : Upper (D 6) (R 6) [10,48,129,68,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3130 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 133 76 274 33 96 196 324), lower := (rows 11 50 133 76 274 33 96 128 256), losses := [{ target := 0, region := (rows 0 34 4 8 17 32 98 136 264), good := (rows 474 114 148 460 338 114 98 128 256) }] }

theorem u3130 : Upper (D 6) (R 6) [10,48,129,68,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3131 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 3, region := 306, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 133 76 274 36 65 224 352), lower := (rows 11 50 133 76 274 36 65 128 256), losses := [] }

theorem u3131 : Upper (D 6) (R 6) [10,48,129,68,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3132 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 50 133 76 274 36 96 193 321), lower := (rows 11 50 133 76 274 36 96 128 256), losses := [] }

theorem u3132 : Upper (D 6) (R 6) [10,48,129,68,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3133 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 3, region := 306, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 133 76 274 96 65 164 292), lower := (rows 11 50 133 76 274 96 65 128 256), losses := [] }

theorem u3133 : Upper (D 6) (R 6) [10,48,129,68,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3134 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 133 76 274 96 68 161 289), lower := (rows 11 50 133 76 274 96 68 128 256), losses := [] }

theorem u3134 : Upper (D 6) (R 6) [10,48,129,68,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3135 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 133 76 274 96 96 133 261), lower := (rows 11 50 133 76 274 96 96 128 256), losses := [] }

theorem u3135 : Upper (D 6) (R 6) [10,48,129,68,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3136 : PairBound 9 := { available := 96, camps := [], pairs := [(2,1),(3,0),(4,1)], upper := (rows 11 50 133 76 276 33 66 224 352), lower := (rows 11 50 133 76 276 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 67 162 290), good := (rows 458 498 204 76 284 480 450 128 256) },{ target := 1, region := (rows 1 0 5 8 25 37 64 136 264), good := (rows 445 48 181 508 308 53 64 128 256) }] }

theorem u3136 : Upper (D 6) (R 6) [10,48,129,68,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3137 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 104, targets := 2 }], pairs := [(1,2),(3,1),(4,0)], upper := (rows 11 50 133 76 276 33 96 194 322), lower := (rows 11 50 133 76 276 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 32 98 131 259), good := (rows 458 498 404 92 276 480 96 128 256) },{ target := 2, region := (rows 1 18 0 8 16 37 127 147 275), good := (rows 491 498 481 104 498 481 96 128 256) }] }

theorem u3137 : Upper (D 6) (R 6) [10,48,129,68,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3138 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 306, targets := 1 },{ cop := 2, region := 72, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 50 133 76 276 96 65 162 290), lower := (rows 11 50 133 76 276 96 65 128 256), losses := [] }

theorem u3138 : Upper (D 6) (R 6) [10,48,129,68,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3139 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 11 50 133 76 276 96 66 161 289), lower := (rows 11 50 133 76 276 96 66 128 256), losses := [] }

theorem u3139 : Upper (D 6) (R 6) [10,48,129,68,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3140 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 133 76 276 96 96 131 259), lower := (rows 11 50 133 76 276 96 96 128 256), losses := [] }

theorem u3140 : Upper (D 6) (R 6) [10,48,129,68,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3141 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 164, targets := 66 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 50 133 76 336 33 66 164 292), lower := (rows 11 50 133 76 336 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 67 128 256), good := (rows 74 114 204 76 336 96 66 128 256) }] }

theorem u3141 : Upper (D 6) (R 6) [10,48,129,68,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3142 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 133 76 336 33 68 162 290), lower := (rows 11 50 133 76 336 33 68 128 256), losses := [] }

theorem u3142 : Upper (D 6) (R 6) [10,48,129,68,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3143 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 132, targets := 32 },{ cop := 0, region := 132, targets := 64 },{ cop := 2, region := 104, targets := 2 }], pairs := [(2,5),(2,6),(3,1)], upper := (rows 11 50 133 76 336 33 96 134 262), lower := (rows 11 50 133 76 336 33 96 128 256), losses := [] }

theorem u3143 : Upper (D 6) (R 6) [10,48,129,68,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3144 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 306, targets := 1 },{ cop := 0, region := 164, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 50 133 76 336 36 65 162 290), lower := (rows 11 50 133 76 336 36 65 128 256), losses := [] }

theorem u3144 : Upper (D 6) (R 6) [10,48,129,68,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3145 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 164, targets := 66 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 50 133 76 336 36 66 161 289), lower := (rows 11 50 133 76 336 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 44 67 128 256), good := (rows 106 114 236 108 336 44 66 128 256) }] }

theorem u3145 : Upper (D 6) (R 6) [10,48,129,68,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3146 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 0, region := 132, targets := 32 }], pairs := [(2,5),(3,0),(3,1)], upper := (rows 11 50 133 76 336 36 96 131 259), lower := (rows 11 50 133 76 336 36 96 128 256), losses := [] }

theorem u3146 : Upper (D 6) (R 6) [10,48,129,68,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3147 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 133 104 273 36 66 196 324), lower := (rows 11 50 133 104 273 36 66 128 256), losses := [] }

theorem u3147 : Upper (D 6) (R 6) [10,48,129,96,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3148 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 275, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 133 104 273 36 68 194 322), lower := (rows 11 50 133 104 273 36 68 128 256), losses := [] }

theorem u3148 : Upper (D 6) (R 6) [10,48,129,96,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3149 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 164, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 50 133 268 81 36 66 224 352), lower := (rows 11 50 133 268 81 36 66 128 256), losses := [] }

theorem u3149 : Upper (D 6) (R 6) [10,48,129,260,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3150 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 2 }], pairs := [(3,0),(4,1),(4,2)], upper := (rows 11 50 133 268 81 36 96 194 322), lower := (rows 11 50 133 268 81 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 44 111 131 259), good := (rows 490 498 492 364 464 108 96 128 256) },{ target := 2, region := (rows 1 2 0 8 17 32 98 131 259), good := (rows 475 498 401 264 465 96 96 128 256) }] }

theorem u3150 : Upper (D 6) (R 6) [10,48,129,260,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3151 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 133 268 82 33 68 224 352), lower := (rows 11 50 133 268 82 33 68 128 256), losses := [{ target := 0, region := (rows 0 34 4 8 17 32 76 128 256), good := (rows 90 50 212 332 82 50 68 128 256) }] }

theorem u3151 : Upper (D 6) (R 6) [10,48,129,260,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3152 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 82, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 133 268 82 33 96 196 324), lower := (rows 11 50 133 268 82 33 96 128 256), losses := [] }

theorem u3152 : Upper (D 6) (R 6) [10,48,129,260,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3153 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 50 133 268 82 36 65 224 352), lower := (rows 11 50 133 268 82 36 65 128 256), losses := [] }

theorem u3153 : Upper (D 6) (R 6) [10,48,129,260,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3154 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 82, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 133 268 82 36 96 193 321), lower := (rows 11 50 133 268 82 36 96 128 256), losses := [] }

theorem u3154 : Upper (D 6) (R 6) [10,48,129,260,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3155 : PairBound 9 := { available := 96, camps := [], pairs := [(1,2),(3,1),(4,0)], upper := (rows 11 50 133 268 84 33 66 224 352), lower := (rows 11 50 133 268 84 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 32 67 162 290), good := (rows 458 498 212 284 84 480 450 128 256) },{ target := 1, region := (rows 1 0 4 24 16 37 64 144 272), good := (rows 41 440 165 300 508 33 64 128 256) },{ target := 2, region := (rows 1 18 0 8 16 37 83 183 311), good := (rows 491 498 481 424 498 481 450 128 256) }] }

theorem u3155 : Upper (D 6) (R 6) [10,48,129,260,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3156 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 2 }], pairs := [(1,2),(3,0),(4,1)], upper := (rows 11 50 133 268 84 33 96 194 322), lower := (rows 11 50 133 268 84 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 98 131 259), good := (rows 458 498 396 268 92 480 96 128 256) },{ target := 2, region := (rows 1 18 0 8 16 37 127 147 275), good := (rows 491 498 481 360 498 481 96 128 256) }] }

theorem u3156 : Upper (D 6) (R 6) [10,48,129,260,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3157 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 133 296 81 36 66 196 324), lower := (rows 11 50 133 296 81 36 66 128 256), losses := [] }

theorem u3157 : Upper (D 6) (R 6) [10,48,129,288,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3158 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 2, region := 80, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 11 50 133 296 81 36 68 194 322), lower := (rows 11 50 133 296 81 36 68 128 256), losses := [] }

theorem u3158 : Upper (D 6) (R 6) [10,48,129,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3159 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 50 133 328 22 96 65 164 292), lower := (rows 11 50 133 328 22 96 65 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 125 69 128 256), good := (rows 107 50 225 360 114 96 97 128 256) }] }

theorem u3159 : Upper (D 6) (R 6) [10,48,129,320,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3160 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 133 328 22 96 68 161 289), lower := (rows 11 50 133 328 22 96 68 128 256), losses := [] }

theorem u3160 : Upper (D 6) (R 6) [10,48,129,320,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3161 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 148, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 133 328 22 96 96 133 261), lower := (rows 11 50 133 328 22 96 96 128 256), losses := [] }

theorem u3161 : Upper (D 6) (R 6) [10,48,129,320,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3162 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 164, targets := 66 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 50 133 328 81 36 66 164 292), lower := (rows 11 50 133 328 81 36 66 128 256), losses := [] }

theorem u3162 : Upper (D 6) (R 6) [10,48,129,320,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3163 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 166, targets := 64 },{ cop := 2, region := 80, targets := 2 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 50 133 328 81 36 68 162 290), lower := (rows 11 50 133 328 81 36 68 128 256), losses := [] }

theorem u3163 : Upper (D 6) (R 6) [10,48,129,320,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3164 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 166, targets := 64 },{ cop := 0, region := 132, targets := 32 }], pairs := [(1,6),(2,5),(2,6)], upper := (rows 11 50 133 328 81 36 96 134 262), lower := (rows 11 50 133 328 81 36 96 128 256), losses := [] }

theorem u3164 : Upper (D 6) (R 6) [10,48,129,320,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3165 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 50 134 44 273 96 65 196 324), lower := (rows 11 50 134 44 273 96 65 128 256), losses := [] }

theorem u3165 : Upper (D 6) (R 6) [10,48,130,36,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3166 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 104, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 50 134 44 273 96 68 193 321), lower := (rows 11 50 134 44 273 96 68 128 256), losses := [] }

theorem u3166 : Upper (D 6) (R 6) [10,48,130,36,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3167 : Route 9 := (fun mask => (mask,id))

def c3167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3167 : Upper (D 6) (R 6) [10,48,130,36,260,64,1] 13 := by
  apply FastRouting.sound _ _ [10,48,130,36,260,64,1] 13 (by decide) (choices 1) [1,64] r3167 c3167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u220
  · exact u221

def b3168 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 50 134 73 84 288 65 164 292), lower := (rows 11 50 134 73 84 288 65 128 256), losses := [] }

theorem u3168 : Upper (D 6) (R 6) [10,48,130,65,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3168 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3169 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 50 134 73 84 288 68 161 289), lower := (rows 11 50 134 73 84 288 68 128 256), losses := [] }

theorem u3169 : Upper (D 6) (R 6) [10,48,130,65,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3169 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3170 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 50 134 73 84 288 96 133 261), lower := (rows 11 50 134 73 84 288 96 128 256), losses := [] }

theorem u3170 : Upper (D 6) (R 6) [10,48,130,65,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3170 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3171 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 4, region := 230, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 50 134 73 273 36 68 224 352), lower := (rows 11 50 134 73 273 36 68 128 256), losses := [] }

theorem u3171 : Upper (D 6) (R 6) [10,48,130,65,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3172 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 230, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 134 73 273 36 96 196 324), lower := (rows 11 50 134 73 273 36 96 128 256), losses := [] }

theorem u3172 : Upper (D 6) (R 6) [10,48,130,65,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3173 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 50 134 73 276 96 65 164 292), lower := (rows 11 50 134 73 276 96 65 128 256), losses := [] }

theorem u3173 : Upper (D 6) (R 6) [10,48,130,65,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3174 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 50 134 73 276 96 68 161 289), lower := (rows 11 50 134 73 276 96 68 128 256), losses := [] }

theorem u3174 : Upper (D 6) (R 6) [10,48,130,65,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3175 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 134 73 276 96 96 133 261), lower := (rows 11 50 134 73 276 96 96 128 256), losses := [] }

theorem u3175 : Upper (D 6) (R 6) [10,48,130,65,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3176 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 134 73 336 36 65 164 292), lower := (rows 11 50 134 73 336 36 65 128 256), losses := [] }

theorem u3176 : Upper (D 6) (R 6) [10,48,130,65,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3177 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 0, region := 164, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 50 134 73 336 36 68 161 289), lower := (rows 11 50 134 73 336 36 68 128 256), losses := [] }

theorem u3177 : Upper (D 6) (R 6) [10,48,130,65,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3178 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 0, region := 132, targets := 32 }], pairs := [(0,2),(2,5),(3,2)], upper := (rows 11 50 134 73 336 36 96 133 261), lower := (rows 11 50 134 73 336 36 96 128 256), losses := [] }

theorem u3178 : Upper (D 6) (R 6) [10,48,130,65,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3179 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 50 134 76 21 96 65 416 288), lower := (rows 11 50 134 76 21 96 65 128 256), losses := [] }

theorem u3179 : Upper (D 6) (R 6) [10,48,130,68,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3179
end Delivery.IrregularNine14.P06
