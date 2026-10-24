import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7500 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 293, targets := 64 }], pairs := [(0,6),(2,6),(4,0)], upper := (rows 35 138 276 73 82 36 68 161 289), lower := (rows 35 138 276 73 82 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 100 100 128 256), good := (rows 114 138 372 120 114 100 100 128 256) }] }

theorem u7500 : Upper (D 6) (R 6) [34,136,272,65,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7501 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 276 73 82 36 96 133 261), lower := (rows 35 138 276 73 82 36 96 128 256), losses := [] }

theorem u7501 : Upper (D 6) (R 6) [34,136,272,65,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7502 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 138 276 73 112 36 65 134 262), lower := (rows 35 138 276 73 112 36 65 128 256), losses := [] }

theorem u7502 : Upper (D 6) (R 6) [34,136,272,65,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7503 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 3, region := 308, targets := 2 }], pairs := [(2,1),(3,2),(4,2)], upper := (rows 35 138 276 73 112 36 66 133 261), lower := (rows 35 138 276 73 112 36 66 128 256), losses := [] }

theorem u7503 : Upper (D 6) (R 6) [34,136,272,65,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7504 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 276 73 112 36 68 131 259), lower := (rows 35 138 276 73 112 36 68 128 256), losses := [] }

theorem u7504 : Upper (D 6) (R 6) [34,136,272,65,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7505 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 138 276 74 112 36 65 133 261), lower := (rows 35 138 276 74 112 36 65 128 256), losses := [] }

theorem u7505 : Upper (D 6) (R 6) [34,136,272,66,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7506 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 276 74 112 36 68 129 257), lower := (rows 35 138 276 74 112 36 68 128 256), losses := [] }

theorem u7506 : Upper (D 6) (R 6) [34,136,272,66,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7507 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 138 276 104 81 36 65 134 262), lower := (rows 35 138 276 104 81 36 65 128 256), losses := [] }

theorem u7507 : Upper (D 6) (R 6) [34,136,272,96,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7508 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,2),(4,2)], upper := (rows 35 138 276 104 81 36 66 133 261), lower := (rows 35 138 276 104 81 36 66 128 256), losses := [] }

theorem u7508 : Upper (D 6) (R 6) [34,136,272,96,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7509 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 138 276 104 81 36 68 131 259), lower := (rows 35 138 276 104 81 36 68 128 256), losses := [] }

theorem u7509 : Upper (D 6) (R 6) [34,136,272,96,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7510 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 3, region := 210, targets := 32 }], pairs := [(0,2),(1,5),(4,2)], upper := (rows 35 138 292 13 81 96 66 148 276), lower := (rows 35 138 292 13 81 96 66 128 256), losses := [] }

theorem u7510 : Upper (D 6) (R 6) [34,136,288,5,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7511 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 8, region := 100, targets := 1 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 35 138 292 13 81 96 68 146 274), lower := (rows 35 138 292 13 81 96 68 128 256), losses := [] }

theorem u7511 : Upper (D 6) (R 6) [34,136,288,5,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7512 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 292 13 81 96 80 134 262), lower := (rows 35 138 292 13 81 96 80 128 256), losses := [] }

theorem u7512 : Upper (D 6) (R 6) [34,136,288,5,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7512 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7513 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 138 292 13 84 96 65 146 274), lower := (rows 35 138 292 13 84 96 65 128 256), losses := [] }

theorem u7513 : Upper (D 6) (R 6) [34,136,288,5,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7514 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 138 292 13 84 96 66 145 273), lower := (rows 35 138 292 13 84 96 66 128 256), losses := [] }

theorem u7514 : Upper (D 6) (R 6) [34,136,288,5,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7515 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 292 13 84 96 80 131 259), lower := (rows 35 138 292 13 84 96 80 128 256), losses := [] }

theorem u7515 : Upper (D 6) (R 6) [34,136,288,5,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7515 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7516 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 138 292 14 81 96 65 148 276), lower := (rows 35 138 292 14 81 96 65 128 256), losses := [] }

theorem u7516 : Upper (D 6) (R 6) [34,136,288,6,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7517 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 292 14 81 96 68 145 273), lower := (rows 35 138 292 14 81 96 68 128 256), losses := [] }

theorem u7517 : Upper (D 6) (R 6) [34,136,288,6,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7518 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 292 14 81 96 80 133 261), lower := (rows 35 138 292 14 81 96 80 128 256), losses := [] }

theorem u7518 : Upper (D 6) (R 6) [34,136,288,6,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7518 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7519 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 292 14 84 96 65 145 273), lower := (rows 35 138 292 14 84 96 65 128 256), losses := [] }

theorem u7519 : Upper (D 6) (R 6) [34,136,288,6,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7520 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 292 14 84 96 80 129 257), lower := (rows 35 138 292 14 84 96 80 128 256), losses := [] }

theorem u7520 : Upper (D 6) (R 6) [34,136,288,6,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7520 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7521 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 105, targets := 4 },{ cop := 5, region := 260, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 35 138 292 25 22 96 65 196 324), lower := (rows 35 138 292 25 22 96 65 128 256), losses := [] }

theorem u7521 : Upper (D 6) (R 6) [34,136,288,17,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7522 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 100, targets := 3 }], pairs := [(1,5),(2,0),(2,1)], upper := (rows 35 138 292 25 22 96 68 193 321), lower := (rows 35 138 292 25 22 96 68 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 16 0 84 136 264), good := (rows 3 394 324 475 86 64 68 128 256) }] }

theorem u7522 : Upper (D 6) (R 6) [34,136,288,17,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7523 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 260, targets := 1 },{ cop := 0, region := 260, targets := 64 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 35 138 292 25 84 96 65 134 262), lower := (rows 35 138 292 25 84 96 65 128 256), losses := [] }

theorem u7523 : Upper (D 6) (R 6) [34,136,288,17,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7524 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 66 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 35 138 292 25 84 96 66 133 261), lower := (rows 35 138 292 25 84 96 66 128 256), losses := [] }

theorem u7524 : Upper (D 6) (R 6) [34,136,288,17,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7525 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 292 25 84 96 68 131 259), lower := (rows 35 138 292 25 84 96 68 128 256), losses := [] }

theorem u7525 : Upper (D 6) (R 6) [34,136,288,17,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7526 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 146, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 138 292 76 22 33 65 208 336), lower := (rows 35 138 292 76 22 33 65 128 256), losses := [] }

theorem u7526 : Upper (D 6) (R 6) [34,136,288,68,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7527 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 138 292 76 22 33 80 193 321), lower := (rows 35 138 292 76 22 33 80 128 256), losses := [] }

theorem u7527 : Upper (D 6) (R 6) [34,136,288,68,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7527 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7528 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 292, targets := 2 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 35 138 292 76 81 33 66 148 276), lower := (rows 35 138 292 76 81 33 66 128 256), losses := [] }

theorem u7528 : Upper (D 6) (R 6) [34,136,288,68,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7529 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 292 76 81 33 68 146 274), lower := (rows 35 138 292 76 81 33 68 128 256), losses := [] }

theorem u7529 : Upper (D 6) (R 6) [34,136,288,68,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7530 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 292 76 81 33 80 134 262), lower := (rows 35 138 292 76 81 33 80 128 256), losses := [] }

theorem u7530 : Upper (D 6) (R 6) [34,136,288,68,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7530 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7531 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 138 292 76 81 48 65 134 262), lower := (rows 35 138 292 76 81 48 65 128 256), losses := [] }

theorem u7531 : Upper (D 6) (R 6) [34,136,288,68,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7531 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7532 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 138 292 76 81 48 66 133 261), lower := (rows 35 138 292 76 81 48 66 128 256), losses := [] }

theorem u7532 : Upper (D 6) (R 6) [34,136,288,68,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7532 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7533 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 138 292 76 81 48 68 131 259), lower := (rows 35 138 292 76 81 48 68 128 256), losses := [] }

theorem u7533 : Upper (D 6) (R 6) [34,136,288,68,65,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7533 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7534 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 138 324 13 22 96 65 176 304), lower := (rows 35 138 324 13 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 10 100 8 25 100 64 217 345), good := (rows 438 410 484 446 438 484 500 128 256) }] }

theorem u7534 : Upper (D 6) (R 6) [34,136,320,5,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7535 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 138 324 13 22 96 80 161 289), lower := (rows 35 138 324 13 22 96 80 128 256), losses := [{ target := 2, region := (rows 25 10 0 8 16 116 80 217 345), good := (rows 419 395 480 427 499 480 497 128 256) }] }

theorem u7535 : Upper (D 6) (R 6) [34,136,320,5,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7535 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7536 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 146, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 138 324 13 22 96 96 145 273), lower := (rows 35 138 324 13 22 96 96 128 256), losses := [] }

theorem u7536 : Upper (D 6) (R 6) [34,136,320,5,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7537 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 138 324 25 82 36 65 164 292), lower := (rows 35 138 324 25 82 36 65 128 256), losses := [] }

theorem u7537 : Upper (D 6) (R 6) [34,136,320,17,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7538 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 68, targets := 3 },{ cop := 8, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 138 324 25 82 36 68 161 289), lower := (rows 35 138 324 25 82 36 68 128 256), losses := [] }

theorem u7538 : Upper (D 6) (R 6) [34,136,320,17,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7539 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(3,2),(4,2)], upper := (rows 35 138 324 25 82 36 96 133 261), lower := (rows 35 138 324 25 82 36 96 128 256), losses := [] }

theorem u7539 : Upper (D 6) (R 6) [34,136,320,17,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7540 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 324 26 21 96 65 164 292), lower := (rows 35 138 324 26 21 96 65 128 256), losses := [] }

theorem u7540 : Upper (D 6) (R 6) [34,136,320,18,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7541 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 8, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 324 26 21 96 68 161 289), lower := (rows 35 138 324 26 21 96 68 128 256), losses := [] }

theorem u7541 : Upper (D 6) (R 6) [34,136,320,18,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7542 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 138, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 138 324 26 21 96 96 133 261), lower := (rows 35 138 324 26 21 96 96 128 256), losses := [] }

theorem u7542 : Upper (D 6) (R 6) [34,136,320,18,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7543 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 138 324 26 81 36 65 164 292), lower := (rows 35 138 324 26 81 36 65 128 256), losses := [] }

theorem u7543 : Upper (D 6) (R 6) [34,136,320,18,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7544 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 8, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 324 26 81 36 68 161 289), lower := (rows 35 138 324 26 81 36 68 128 256), losses := [] }

theorem u7544 : Upper (D 6) (R 6) [34,136,320,18,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7545 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 324 26 81 36 96 133 261), lower := (rows 35 138 324 26 81 36 96 128 256), losses := [] }

theorem u7545 : Upper (D 6) (R 6) [34,136,320,18,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7546 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 138 324 56 81 36 65 134 262), lower := (rows 35 138 324 56 81 36 65 128 256), losses := [] }

theorem u7546 : Upper (D 6) (R 6) [34,136,320,48,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7547 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(3,2),(4,2)], upper := (rows 35 138 324 56 81 36 66 133 261), lower := (rows 35 138 324 56 81 36 66 128 256), losses := [] }

theorem u7547 : Upper (D 6) (R 6) [34,136,320,48,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7548 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 324 56 81 36 68 131 259), lower := (rows 35 138 324 56 81 36 68 128 256), losses := [] }

theorem u7548 : Upper (D 6) (R 6) [34,136,320,48,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7549 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 36 },{ cop := 3, region := 308, targets := 2 }], pairs := [(2,1),(3,2),(3,5)], upper := (rows 35 138 324 73 21 36 66 176 304), lower := (rows 35 138 324 73 21 36 66 128 256), losses := [] }

theorem u7549 : Upper (D 6) (R 6) [34,136,320,65,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7550 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 138 324 73 21 36 80 162 290), lower := (rows 35 138 324 73 21 36 80 128 256), losses := [] }

theorem u7550 : Upper (D 6) (R 6) [34,136,320,65,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7550 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7551 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 324 73 21 36 96 146 274), lower := (rows 35 138 324 73 21 36 96 128 256), losses := [] }

theorem u7551 : Upper (D 6) (R 6) [34,136,320,65,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7552 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 324 73 22 36 65 176 304), lower := (rows 35 138 324 73 22 36 65 128 256), losses := [] }

theorem u7552 : Upper (D 6) (R 6) [34,136,320,65,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7553 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 292, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1)], upper := (rows 35 138 324 73 22 36 80 161 289), lower := (rows 35 138 324 73 22 36 80 128 256), losses := [] }

theorem u7553 : Upper (D 6) (R 6) [34,136,320,65,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7553 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7554 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 324 73 22 36 96 145 273), lower := (rows 35 138 324 73 22 36 96 128 256), losses := [] }

theorem u7554 : Upper (D 6) (R 6) [34,136,320,65,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7555 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 138 324 74 21 36 65 176 304), lower := (rows 35 138 324 74 21 36 65 128 256), losses := [] }

theorem u7555 : Upper (D 6) (R 6) [34,136,320,66,5,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7556 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 324 74 21 36 80 161 289), lower := (rows 35 138 324 74 21 36 80 128 256), losses := [] }

theorem u7556 : Upper (D 6) (R 6) [34,136,320,66,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7556 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7557 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 72, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 35 138 324 74 21 36 96 145 273), lower := (rows 35 138 324 74 21 36 96 128 256), losses := [] }

theorem u7557 : Upper (D 6) (R 6) [34,136,320,66,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7558 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 25 84 288 65 134 262), lower := (rows 35 194 44 25 84 288 65 128 256), losses := [] }

theorem u7558 : Upper (D 6) (R 6) [34,192,40,17,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7558 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7559 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 44 25 84 288 66 133 261), lower := (rows 35 194 44 25 84 288 66 128 256), losses := [] }

theorem u7559 : Upper (D 6) (R 6) [34,192,40,17,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7559 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7559
end Delivery.IrregularNine14.P06
