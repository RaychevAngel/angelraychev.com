import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0006

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5400 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,5),(3,5)], upper := (rows 25 35 196 14 304 96 66 133 261), lower := (rows 25 35 196 14 304 96 66 128 256), losses := [] }

theorem u5400 : Upper (D 6) (R 6) [24,33,192,6,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5401 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 25 35 196 14 304 96 68 131 259), lower := (rows 25 35 196 14 304 96 68 128 256), losses := [] }

theorem u5401 : Upper (D 6) (R 6) [24,33,192,6,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5402 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 25 35 196 73 274 36 66 164 292), lower := (rows 25 35 196 73 274 36 66 128 256), losses := [] }

theorem u5402 : Upper (D 6) (R 6) [24,33,192,65,258,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5403 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 272, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 35 196 73 274 36 68 162 290), lower := (rows 25 35 196 73 274 36 68 128 256), losses := [] }

theorem u5403 : Upper (D 6) (R 6) [24,33,192,65,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5404 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 72, targets := 2 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 25 35 196 73 274 36 96 134 262), lower := (rows 25 35 196 73 274 36 96 128 256), losses := [] }

theorem u5404 : Upper (D 6) (R 6) [24,33,192,65,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5405 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 25 35 196 74 273 36 66 164 292), lower := (rows 25 35 196 74 273 36 66 128 256), losses := [] }

theorem u5405 : Upper (D 6) (R 6) [24,33,192,66,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5406 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 272, targets := 4 }], pairs := [(2,0),(3,0),(4,2)], upper := (rows 25 35 196 74 273 36 68 162 290), lower := (rows 25 35 196 74 273 36 68 128 256), losses := [] }

theorem u5406 : Upper (D 6) (R 6) [24,33,192,66,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5407 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 196 74 273 36 96 134 262), lower := (rows 25 35 196 74 273 36 96 128 256), losses := [] }

theorem u5407 : Upper (D 6) (R 6) [24,33,192,66,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5408 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 25 35 196 74 274 36 65 164 292), lower := (rows 25 35 196 74 274 36 65 128 256), losses := [] }

theorem u5408 : Upper (D 6) (R 6) [24,33,192,66,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5409 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 7, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 25 35 196 74 274 36 68 161 289), lower := (rows 25 35 196 74 274 36 68 128 256), losses := [] }

theorem u5409 : Upper (D 6) (R 6) [24,33,192,66,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5410 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 196 74 274 36 96 133 261), lower := (rows 25 35 196 74 274 36 96 128 256), losses := [] }

theorem u5410 : Upper (D 6) (R 6) [24,33,192,66,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5411 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 1, region := 72, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 196 74 276 36 65 162 290), lower := (rows 25 35 196 74 276 36 65 128 256), losses := [] }

theorem u5411 : Upper (D 6) (R 6) [24,33,192,66,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5412 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 25 35 196 74 276 36 66 161 289), lower := (rows 25 35 196 74 276 36 66 128 256), losses := [] }

theorem u5412 : Upper (D 6) (R 6) [24,33,192,66,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5413 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 196 74 276 36 96 131 259), lower := (rows 25 35 196 74 276 36 96 128 256), losses := [] }

theorem u5413 : Upper (D 6) (R 6) [24,33,192,66,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5414 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 196 74 304 36 65 134 262), lower := (rows 25 35 196 74 304 36 65 128 256), losses := [] }

theorem u5414 : Upper (D 6) (R 6) [24,33,192,66,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5415 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 25 35 196 74 304 36 66 133 261), lower := (rows 25 35 196 74 304 36 66 128 256), losses := [] }

theorem u5415 : Upper (D 6) (R 6) [24,33,192,66,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5416 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 25 35 196 74 304 36 68 131 259), lower := (rows 25 35 196 74 304 36 68 128 256), losses := [] }

theorem u5416 : Upper (D 6) (R 6) [24,33,192,66,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5417 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 38 70 11 148 288 65 224 352), lower := (rows 25 38 70 11 148 288 65 128 256), losses := [] }

theorem u5417 : Upper (D 6) (R 6) [24,36,66,3,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5417 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5418 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 25 38 70 11 148 288 96 193 321), lower := (rows 25 38 70 11 148 288 96 128 256), losses := [] }

theorem u5418 : Upper (D 6) (R 6) [24,36,66,3,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5418 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5419 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 38 70 11 176 288 65 196 324), lower := (rows 25 38 70 11 176 288 65 128 256), losses := [] }

theorem u5419 : Upper (D 6) (R 6) [24,36,66,3,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5419 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5420 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 25 38 70 11 176 288 68 193 321), lower := (rows 25 38 70 11 176 288 68 128 256), losses := [] }

theorem u5420 : Upper (D 6) (R 6) [24,36,66,3,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5420 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5421 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 38 70 11 208 288 65 164 292), lower := (rows 25 38 70 11 208 288 65 128 256), losses := [] }

theorem u5421 : Upper (D 6) (R 6) [24,36,66,3,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5421 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5422 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 25 38 70 11 208 288 68 161 289), lower := (rows 25 38 70 11 208 288 68 128 256), losses := [] }

theorem u5422 : Upper (D 6) (R 6) [24,36,66,3,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5422 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5423 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 25 38 70 11 208 288 96 133 261), lower := (rows 25 38 70 11 208 288 96 128 256), losses := [] }

theorem u5423 : Upper (D 6) (R 6) [24,36,66,3,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5423 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5424 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 38 70 41 146 288 65 196 324), lower := (rows 25 38 70 41 146 288 65 128 256), losses := [] }

theorem u5424 : Upper (D 6) (R 6) [24,36,66,33,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5424 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5425 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 25 38 70 41 146 288 68 193 321), lower := (rows 25 38 70 41 146 288 68 128 256), losses := [] }

theorem u5425 : Upper (D 6) (R 6) [24,36,66,33,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5425 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5426 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 38 70 41 148 288 65 194 322), lower := (rows 25 38 70 41 148 288 65 128 256), losses := [] }

theorem u5426 : Upper (D 6) (R 6) [24,36,66,33,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5426 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5427 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 25 38 70 41 148 288 66 193 321), lower := (rows 25 38 70 41 148 288 66 128 256), losses := [] }

theorem u5427 : Upper (D 6) (R 6) [24,36,66,33,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5427 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5428 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 38 70 41 208 288 65 134 262), lower := (rows 25 38 70 41 208 288 65 128 256), losses := [] }

theorem u5428 : Upper (D 6) (R 6) [24,36,66,33,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5428 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5429 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 25 38 70 41 208 288 66 133 261), lower := (rows 25 38 70 41 208 288 66 128 256), losses := [] }

theorem u5429 : Upper (D 6) (R 6) [24,36,66,33,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5429 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5430 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 25 38 70 41 208 288 68 131 259), lower := (rows 25 38 70 41 208 288 68 128 256), losses := [] }

theorem u5430 : Upper (D 6) (R 6) [24,36,66,33,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5430 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5431 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 70 104 146 33 65 388 260), lower := (rows 25 38 70 104 146 33 65 128 256), losses := [] }

theorem u5431 : Upper (D 6) (R 6) [24,36,66,96,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5432 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 104 146 33 68 385 257), lower := (rows 25 38 70 104 146 33 68 128 256), losses := [] }

theorem u5432 : Upper (D 6) (R 6) [24,36,66,96,130,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5433 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 38 70 104 146 33 320 133 261), lower := (rows 25 38 70 104 146 33 320 128 256), losses := [] }

theorem u5433 : Upper (D 6) (R 6) [24,36,66,96,130,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5433 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5434 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 70 104 400 33 65 134 262), lower := (rows 25 38 70 104 400 33 65 128 256), losses := [] }

theorem u5434 : Upper (D 6) (R 6) [24,36,66,96,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5435 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 70 104 400 33 66 133 261), lower := (rows 25 38 70 104 400 33 66 128 256), losses := [] }

theorem u5435 : Upper (D 6) (R 6) [24,36,66,96,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5436 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 104 400 33 68 131 259), lower := (rows 25 38 70 104 400 33 68 128 256), losses := [] }

theorem u5436 : Upper (D 6) (R 6) [24,36,66,96,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5437 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 136, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 25 38 70 138 304 33 65 196 324), lower := (rows 25 38 70 138 304 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 14 18 32 64 132 260), good := (rows 24 446 478 154 304 32 64 128 256) }] }

theorem u5437 : Upper (D 6) (R 6) [24,36,66,130,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5438 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 138 304 33 68 193 321), lower := (rows 25 38 70 138 304 33 68 128 256), losses := [] }

theorem u5438 : Upper (D 6) (R 6) [24,36,66,130,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5439 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 136, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 25 38 70 138 336 33 65 164 292), lower := (rows 25 38 70 138 336 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 14 20 32 64 130 258), good := (rows 24 446 478 394 336 32 64 128 256) }] }

theorem u5439 : Upper (D 6) (R 6) [24,36,66,130,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5440 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 138 336 33 68 161 289), lower := (rows 25 38 70 138 336 33 68 128 256), losses := [] }

theorem u5440 : Upper (D 6) (R 6) [24,36,66,130,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5441 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 70 138 336 33 96 133 261), lower := (rows 25 38 70 138 336 33 96 128 256), losses := [] }

theorem u5441 : Upper (D 6) (R 6) [24,36,66,130,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5442 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 136, targets := 65 },{ cop := 2, region := 272, targets := 1 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 25 38 70 168 336 33 65 134 262), lower := (rows 25 38 70 168 336 33 65 128 256), losses := [] }

theorem u5442 : Upper (D 6) (R 6) [24,36,66,160,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5443 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 70 168 336 33 66 133 261), lower := (rows 25 38 70 168 336 33 66 128 256), losses := [] }

theorem u5443 : Upper (D 6) (R 6) [24,36,66,160,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5444 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 168 336 33 68 131 259), lower := (rows 25 38 70 168 336 33 68 128 256), losses := [] }

theorem u5444 : Upper (D 6) (R 6) [24,36,66,160,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5445 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 25 38 133 11 276 96 66 224 352), lower := (rows 25 38 133 11 276 96 66 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 18 96 64 224 352), good := (rows 25 436 133 25 276 480 496 128 256) }] }

theorem u5445 : Upper (D 6) (R 6) [24,36,129,3,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5446 : Route 9 := (fun mask => (mask,id))

def c5446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5446 : Upper (D 6) (R 6) [24,36,129,3,260,64,32] 13 := by
  apply FastRouting.sound _ _ [24,36,129,3,260,64,32] 13 (by decide) (choices 1) [2,64] r5446 c5446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u399
  · exact u400

def b5447 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 4, region := 73, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 25 38 133 74 274 96 65 164 292), lower := (rows 25 38 133 74 274 96 65 128 256), losses := [] }

theorem u5447 : Upper (D 6) (R 6) [24,36,129,66,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5448 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 3, region := 305, targets := 4 }], pairs := [(0,2),(1,0),(3,0)], upper := (rows 25 38 133 74 274 96 68 161 289), lower := (rows 25 38 133 74 274 96 68 128 256), losses := [] }

theorem u5448 : Upper (D 6) (R 6) [24,36,129,66,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5449 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 405, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 25 38 133 74 274 96 96 133 261), lower := (rows 25 38 133 74 274 96 96 128 256), losses := [] }

theorem u5449 : Upper (D 6) (R 6) [24,36,129,66,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5450 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(0,1),(1,0),(1,6)], upper := (rows 25 38 133 74 276 34 65 224 352), lower := (rows 25 38 133 74 276 34 65 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 26 32 77 130 258), good := (rows 93 500 197 477 340 432 65 128 256) }] }

theorem u5450 : Upper (D 6) (R 6) [24,36,129,66,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5451 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 405, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 25 38 133 74 276 34 96 193 321), lower := (rows 25 38 133 74 276 34 96 128 256), losses := [] }

theorem u5451 : Upper (D 6) (R 6) [24,36,129,66,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5452 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 65 }], pairs := [(3,2),(4,0),(4,6)], upper := (rows 25 38 133 74 276 96 65 162 290), lower := (rows 25 38 133 74 276 96 65 128 256), losses := [{ target := 2, region := (rows 1 2 0 10 16 127 69 138 266), good := (rows 505 490 225 490 368 96 97 128 256) }] }

theorem u5452 : Upper (D 6) (R 6) [24,36,129,66,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5453 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 25 38 133 74 276 96 66 161 289), lower := (rows 25 38 133 74 276 96 66 128 256), losses := [] }

theorem u5453 : Upper (D 6) (R 6) [24,36,129,66,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5454 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 405, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 25 38 133 74 276 96 96 131 259), lower := (rows 25 38 133 74 276 96 96 128 256), losses := [] }

theorem u5454 : Upper (D 6) (R 6) [24,36,129,66,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5455 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 272, targets := 65 }], pairs := [(3,2),(4,0),(4,6)], upper := (rows 25 38 133 74 304 96 65 134 262), lower := (rows 25 38 133 74 304 96 65 128 256), losses := [{ target := 2, region := (rows 1 2 0 10 16 111 69 128 256), good := (rows 121 106 225 106 304 96 97 128 256) }] }

theorem u5455 : Upper (D 6) (R 6) [24,36,129,66,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5456 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 98 }], pairs := [(2,1),(2,5),(2,6)], upper := (rows 25 38 133 74 304 96 66 133 261), lower := (rows 25 38 133 74 304 96 66 128 256), losses := [] }

theorem u5456 : Upper (D 6) (R 6) [24,36,129,66,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5457 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 3, region := 305, targets := 4 }], pairs := [(0,2),(1,0),(3,0)], upper := (rows 25 38 133 74 304 96 68 131 259), lower := (rows 25 38 133 74 304 96 68 128 256), losses := [] }

theorem u5457 : Upper (D 6) (R 6) [24,36,129,66,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5458 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 1, region := 72, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 25 38 133 76 273 96 66 162 290), lower := (rows 25 38 133 76 273 96 66 128 256), losses := [] }

theorem u5458 : Upper (D 6) (R 6) [24,36,129,68,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5459 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 1, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1)], upper := (rows 25 38 133 76 273 96 96 130 258), lower := (rows 25 38 133 76 273 96 96 128 256), losses := [] }

theorem u5459 : Upper (D 6) (R 6) [24,36,129,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5459
end Delivery.IrregularNine14.P06
