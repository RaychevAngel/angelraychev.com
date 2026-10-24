import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0005

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4500 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 403, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 22 104 336 36 68 129 257), lower := (rows 11 162 22 104 336 36 68 128 256), losses := [] }

theorem u4500 : Upper (D 6) (R 6) [10,160,18,96,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4501 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 7, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 162 37 25 276 96 66 196 324), lower := (rows 11 162 37 25 276 96 66 128 256), losses := [] }

theorem u4501 : Upper (D 6) (R 6) [10,160,33,17,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4502 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 11 162 37 25 276 96 68 194 322), lower := (rows 11 162 37 25 276 96 68 128 256), losses := [] }

theorem u4502 : Upper (D 6) (R 6) [10,160,33,17,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4503 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 11 162 37 28 81 288 66 196 324), lower := (rows 11 162 37 28 81 288 66 128 256), losses := [] }

theorem u4503 : Upper (D 6) (R 6) [10,160,33,20,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4503 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4504 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 88, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 11 162 37 28 81 288 68 194 322), lower := (rows 11 162 37 28 81 288 68 128 256), losses := [] }

theorem u4504 : Upper (D 6) (R 6) [10,160,33,20,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4504 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4505 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 11 162 37 28 82 288 65 196 324), lower := (rows 11 162 37 28 82 288 65 128 256), losses := [] }

theorem u4505 : Upper (D 6) (R 6) [10,160,33,20,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4505 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4506 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0)], upper := (rows 11 162 37 28 82 288 68 193 321), lower := (rows 11 162 37 28 82 288 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 288 76 128 256), good := (rows 90 162 124 92 82 288 76 128 288) }] }

theorem u4506 : Upper (D 6) (R 6) [10,160,33,20,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4506 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4507 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(3,5)], upper := (rows 11 162 37 28 273 96 66 196 324), lower := (rows 11 162 37 28 273 96 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 20 0 67 132 260), good := (rows 75 194 477 412 337 64 66 128 256) }] }

theorem u4507 : Upper (D 6) (R 6) [10,160,33,20,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4508 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 108, targets := 2 },{ cop := 5, region := 130, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 162 37 28 273 96 68 194 322), lower := (rows 11 162 37 28 273 96 68 128 256), losses := [] }

theorem u4508 : Upper (D 6) (R 6) [10,160,33,20,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4509 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 11 162 37 28 274 96 65 196 324), lower := (rows 11 162 37 28 274 96 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 17 0 69 140 268), good := (rows 475 130 477 476 274 64 81 128 256) }] }

theorem u4509 : Upper (D 6) (R 6) [10,160,33,20,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4510 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 11 162 37 28 274 96 68 193 321), lower := (rows 11 162 37 28 274 96 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 17 0 76 133 261), good := (rows 475 130 477 476 274 64 460 128 256) }] }

theorem u4510 : Upper (D 6) (R 6) [10,160,33,20,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4511 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 65 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 11 162 37 28 336 96 65 134 262), lower := (rows 11 162 37 28 336 96 65 128 256), losses := [] }

theorem u4511 : Upper (D 6) (R 6) [10,160,33,20,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4512 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 98, targets := 5 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 37 28 336 96 66 133 261), lower := (rows 11 162 37 28 336 96 66 128 256), losses := [] }

theorem u4512 : Upper (D 6) (R 6) [10,160,33,20,320,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4513 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 2, region := 130, targets := 4 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 11 162 37 28 336 96 68 131 259), lower := (rows 11 162 37 28 336 96 68 128 256), losses := [] }

theorem u4513 : Upper (D 6) (R 6) [10,160,33,20,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4514 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 11 162 37 76 82 288 65 148 276), lower := (rows 11 162 37 76 82 288 65 128 256), losses := [] }

theorem u4514 : Upper (D 6) (R 6) [10,160,33,68,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4514 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4515 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 37 76 82 288 68 145 273), lower := (rows 11 162 37 76 82 288 68 128 256), losses := [] }

theorem u4515 : Upper (D 6) (R 6) [10,160,33,68,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4515 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4516 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 11 162 37 76 82 288 80 133 261), lower := (rows 11 162 37 76 82 288 80 128 256), losses := [] }

theorem u4516 : Upper (D 6) (R 6) [10,160,33,68,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4516 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4517 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 37 88 274 36 65 196 324), lower := (rows 11 162 37 88 274 36 65 128 256), losses := [] }

theorem u4517 : Upper (D 6) (R 6) [10,160,33,80,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4518 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(0,5),(2,1),(2,6)], upper := (rows 11 162 37 88 274 36 68 193 321), lower := (rows 11 162 37 88 274 36 68 128 256), losses := [{ target := 5, region := (rows 19 2 4 14 19 0 100 142 270), good := (rows 411 475 477 473 411 460 460 128 256) }] }

theorem u4518 : Upper (D 6) (R 6) [10,160,33,80,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4519 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 11 162 37 265 82 96 68 148 276), lower := (rows 11 162 37 265 82 96 68 128 256), losses := [] }

theorem u4519 : Upper (D 6) (R 6) [10,160,33,257,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4520 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 37 265 82 96 80 132 260), lower := (rows 11 162 37 265 82 96 80 128 256), losses := [] }

theorem u4520 : Upper (D 6) (R 6) [10,160,33,257,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4520 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4521 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 7, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 162 37 265 84 96 66 148 276), lower := (rows 11 162 37 265 84 96 66 128 256), losses := [] }

theorem u4521 : Upper (D 6) (R 6) [10,160,33,257,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4522 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 37 265 84 96 68 146 274), lower := (rows 11 162 37 265 84 96 68 128 256), losses := [] }

theorem u4522 : Upper (D 6) (R 6) [10,160,33,257,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4523 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 37 265 84 96 80 134 262), lower := (rows 11 162 37 265 84 96 80 128 256), losses := [] }

theorem u4523 : Upper (D 6) (R 6) [10,160,33,257,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4523 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4524 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 329, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 162 37 268 22 96 65 208 336), lower := (rows 11 162 37 268 22 96 65 128 256), losses := [] }

theorem u4524 : Upper (D 6) (R 6) [10,160,33,260,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4525 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 37 268 22 96 80 193 321), lower := (rows 11 162 37 268 22 96 80 128 256), losses := [] }

theorem u4525 : Upper (D 6) (R 6) [10,160,33,260,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4525 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4526 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 2 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 162 37 268 81 96 66 148 276), lower := (rows 11 162 37 268 81 96 66 128 256), losses := [] }

theorem u4526 : Upper (D 6) (R 6) [10,160,33,260,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4527 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 162 37 268 81 96 68 146 274), lower := (rows 11 162 37 268 81 96 68 128 256), losses := [] }

theorem u4527 : Upper (D 6) (R 6) [10,160,33,260,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4528 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 37 268 81 96 80 134 262), lower := (rows 11 162 37 268 81 96 80 128 256), losses := [] }

theorem u4528 : Upper (D 6) (R 6) [10,160,33,260,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4528 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4529 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 162 37 268 82 96 65 148 276), lower := (rows 11 162 37 268 82 96 65 128 256), losses := [] }

theorem u4529 : Upper (D 6) (R 6) [10,160,33,260,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4530 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(0,2),(2,1),(4,0)], upper := (rows 11 162 37 268 82 96 68 145 273), lower := (rows 11 162 37 268 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 125 76 128 256), good := (rows 122 162 116 364 114 96 100 128 256) },{ target := 2, region := (rows 9 70 0 8 112 112 64 132 260), good := (rows 11 178 435 395 114 114 498 128 256) }] }

theorem u4530 : Upper (D 6) (R 6) [10,160,33,260,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4531 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 37 268 82 96 80 133 261), lower := (rows 11 162 37 268 82 96 80 128 256), losses := [] }

theorem u4531 : Upper (D 6) (R 6) [10,160,33,260,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4531 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4532 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 162 37 268 84 96 65 146 274), lower := (rows 11 162 37 268 84 96 65 128 256), losses := [] }

theorem u4532 : Upper (D 6) (R 6) [10,160,33,260,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4533 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 162 37 268 84 96 66 145 273), lower := (rows 11 162 37 268 84 96 66 128 256), losses := [{ target := 0, region := (rows 0 130 4 8 20 247 195 128 256), good := (rows 106 226 116 316 116 96 98 226 256) }] }

theorem u4533 : Upper (D 6) (R 6) [10,160,33,260,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4534 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 37 268 84 96 80 131 259), lower := (rows 11 162 37 268 84 96 80 128 256), losses := [] }

theorem u4534 : Upper (D 6) (R 6) [10,160,33,260,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4534 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4535 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 162 37 280 82 36 65 196 324), lower := (rows 11 162 37 280 82 36 65 128 256), losses := [] }

theorem u4535 : Upper (D 6) (R 6) [10,160,33,272,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4536 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 265, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 37 280 82 36 68 193 321), lower := (rows 11 162 37 280 82 36 68 128 256), losses := [] }

theorem u4536 : Upper (D 6) (R 6) [10,160,33,272,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4537 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 130, targets := 65 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 11 162 37 280 82 96 65 132 260), lower := (rows 11 162 37 280 82 96 65 128 256), losses := [] }

theorem u4537 : Upper (D 6) (R 6) [10,160,33,272,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4538 : Route 9 := (fun mask => (mask,id))

def c4538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4538 : Upper (D 6) (R 6) [10,160,33,272,66,64,4] 13 := by
  apply FastRouting.sound _ _ [10,160,33,272,66,64,4] 13 (by decide) (choices 1) [1,4] r4538 c4538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u336
  · exact u337

def b4539 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 162 37 328 82 36 65 148 276), lower := (rows 11 162 37 328 82 36 65 128 256), losses := [] }

theorem u4539 : Upper (D 6) (R 6) [10,160,33,320,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4540 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 265, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 37 328 82 36 68 145 273), lower := (rows 11 162 37 328 82 36 68 128 256), losses := [] }

theorem u4540 : Upper (D 6) (R 6) [10,160,33,320,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4541 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 162 37 328 82 36 80 133 261), lower := (rows 11 162 37 328 82 36 80 128 256), losses := [] }

theorem u4541 : Upper (D 6) (R 6) [10,160,33,320,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4541 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4542 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 162 37 328 84 36 65 146 274), lower := (rows 11 162 37 328 84 36 65 128 256), losses := [] }

theorem u4542 : Upper (D 6) (R 6) [10,160,33,320,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4543 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(4,0)], upper := (rows 11 162 37 328 84 36 66 145 273), lower := (rows 11 162 37 328 84 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 52 67 128 256), good := (rows 74 226 116 328 116 52 66 128 256) }] }

theorem u4543 : Upper (D 6) (R 6) [10,160,33,320,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4544 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 37 328 84 36 80 131 259), lower := (rows 11 162 37 328 84 36 80 128 256), losses := [] }

theorem u4544 : Upper (D 6) (R 6) [10,160,33,320,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4544 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4545 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 162 37 328 84 48 65 134 262), lower := (rows 11 162 37 328 84 48 65 128 256), losses := [] }

theorem u4545 : Upper (D 6) (R 6) [10,160,33,320,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4545 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4546 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 130, targets := 64 }], pairs := [(1,6),(4,0)], upper := (rows 11 162 37 328 84 48 66 133 261), lower := (rows 11 162 37 328 84 48 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 52 67 128 256), good := (rows 74 226 116 328 116 48 66 128 256) }] }

theorem u4546 : Upper (D 6) (R 6) [10,160,33,320,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4546 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4547 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 162 37 328 84 48 68 131 259), lower := (rows 11 162 37 328 84 48 68 128 256), losses := [] }

theorem u4547 : Upper (D 6) (R 6) [10,160,33,320,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4547 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4548 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 52 13 82 288 65 196 324), lower := (rows 11 162 52 13 82 288 65 128 256), losses := [] }

theorem u4548 : Upper (D 6) (R 6) [10,160,48,5,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4548 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4549 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 162 52 13 82 288 68 193 321), lower := (rows 11 162 52 13 82 288 68 128 256), losses := [] }

theorem u4549 : Upper (D 6) (R 6) [10,160,48,5,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4549 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4550 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 7, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 162 52 13 273 96 66 196 324), lower := (rows 11 162 52 13 273 96 66 128 256), losses := [] }

theorem u4550 : Upper (D 6) (R 6) [10,160,48,5,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4551 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 52 13 273 96 68 194 322), lower := (rows 11 162 52 13 273 96 68 128 256), losses := [] }

theorem u4551 : Upper (D 6) (R 6) [10,160,48,5,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4552 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 52 13 274 96 65 196 324), lower := (rows 11 162 52 13 274 96 65 128 256), losses := [] }

theorem u4552 : Upper (D 6) (R 6) [10,160,48,5,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4553 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,5)], upper := (rows 11 162 52 13 274 96 68 193 321), lower := (rows 11 162 52 13 274 96 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 76 137 265), good := (rows 475 130 84 477 274 64 68 128 256) }] }

theorem u4553 : Upper (D 6) (R 6) [10,160,48,5,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4554 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 52 73 84 288 65 134 262), lower := (rows 11 162 52 73 84 288 65 128 256), losses := [] }

theorem u4554 : Upper (D 6) (R 6) [10,160,48,65,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4554 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4555 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 52 73 84 288 66 133 261), lower := (rows 11 162 52 73 84 288 66 128 256), losses := [] }

theorem u4555 : Upper (D 6) (R 6) [10,160,48,65,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4555 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4556 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 419, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 162 52 73 84 288 68 131 259), lower := (rows 11 162 52 73 84 288 68 128 256), losses := [] }

theorem u4556 : Upper (D 6) (R 6) [10,160,48,65,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4556 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4557 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 52 73 274 96 65 132 260), lower := (rows 11 162 52 73 274 96 65 128 256), losses := [] }

theorem u4557 : Upper (D 6) (R 6) [10,160,48,65,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4558 : Route 9 := (fun mask => (mask,id))

def c4558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4558 : Upper (D 6) (R 6) [10,160,48,65,258,64,4] 13 := by
  apply FastRouting.sound _ _ [10,160,48,65,258,64,4] 13 (by decide) (choices 1) [1,4] r4558 c4558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u338
  · exact u339

def b4559 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 52 73 276 96 65 134 262), lower := (rows 11 162 52 73 276 96 65 128 256), losses := [] }

theorem u4559 : Upper (D 6) (R 6) [10,160,48,65,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4559
end Delivery.IrregularNine14.P06
