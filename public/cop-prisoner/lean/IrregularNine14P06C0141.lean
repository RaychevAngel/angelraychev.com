import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8460 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 73, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 134 324 73 52 34 80 131 259), lower := (rows 41 134 324 73 52 34 80 128 256), losses := [] }

theorem u8460 : Upper (D 6) (R 6) [40,132,320,65,36,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8460 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8461 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 162, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 41 134 324 74 21 48 65 162 290), lower := (rows 41 134 324 74 21 48 65 128 256), losses := [] }

theorem u8461 : Upper (D 6) (R 6) [40,132,320,66,5,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8461 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8462 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 72, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 41 134 324 74 21 48 66 161 289), lower := (rows 41 134 324 74 21 48 66 128 256), losses := [] }

theorem u8462 : Upper (D 6) (R 6) [40,132,320,66,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8462 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8463 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 130, targets := 32 },{ cop := 4, region := 130, targets := 64 }], pairs := [(1,5),(1,6)], upper := (rows 41 134 324 74 21 48 96 131 259), lower := (rows 41 134 324 74 21 48 96 128 256), losses := [] }

theorem u8463 : Upper (D 6) (R 6) [40,132,320,66,5,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8463 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8464 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 72, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 134 324 88 19 36 65 162 290), lower := (rows 41 134 324 88 19 36 65 128 256), losses := [] }

theorem u8464 : Upper (D 6) (R 6) [40,132,320,80,3,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8465 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 72, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 134 324 88 19 36 66 161 289), lower := (rows 41 134 324 88 19 36 66 128 256), losses := [] }

theorem u8465 : Upper (D 6) (R 6) [40,132,320,80,3,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8466 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 41 134 324 88 19 36 96 131 259), lower := (rows 41 134 324 88 19 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 260 24 16 294 375 128 256), good := (rows 104 230 356 88 122 100 96 128 356) }] }

theorem u8466 : Upper (D 6) (R 6) [40,132,320,80,3,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8467 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 72, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 134 324 88 21 34 65 162 290), lower := (rows 41 134 324 88 21 34 65 128 256), losses := [] }

theorem u8467 : Upper (D 6) (R 6) [40,132,320,80,5,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8468 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 41 134 324 88 21 34 66 161 289), lower := (rows 41 134 324 88 21 34 66 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 98 98 137 265), good := (rows 489 226 352 505 401 98 98 128 256) },{ target := 6, region := (rows 9 18 4 8 16 122 0 153 281), good := (rows 425 166 292 443 439 34 34 128 256) }] }

theorem u8468 : Upper (D 6) (R 6) [40,132,320,80,5,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8469 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 130, targets := 32 },{ cop := 4, region := 130, targets := 64 }], pairs := [(1,5),(1,6),(3,0)], upper := (rows 41 134 324 88 21 34 96 131 259), lower := (rows 41 134 324 88 21 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 34 99 128 256), good := (rows 104 230 324 88 92 98 96 128 256) }] }

theorem u8469 : Upper (D 6) (R 6) [40,132,320,80,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8470 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 146 292 11 22 96 65 196 324), lower := (rows 41 146 292 11 22 96 65 128 256), losses := [] }

theorem u8470 : Upper (D 6) (R 6) [40,144,288,3,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8471 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 146 292 11 22 96 68 193 321), lower := (rows 41 146 292 11 22 96 68 128 256), losses := [] }

theorem u8471 : Upper (D 6) (R 6) [40,144,288,3,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8472 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 41 146 292 14 19 96 65 196 324), lower := (rows 41 146 292 14 19 96 65 128 256), losses := [] }

theorem u8472 : Upper (D 6) (R 6) [40,144,288,6,3,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8473 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 146 292 14 19 96 68 193 321), lower := (rows 41 146 292 14 19 96 68 128 256), losses := [] }

theorem u8473 : Upper (D 6) (R 6) [40,144,288,6,3,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8474 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 146 292 14 81 96 65 134 262), lower := (rows 41 146 292 14 81 96 65 128 256), losses := [] }

theorem u8474 : Upper (D 6) (R 6) [40,144,288,6,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8475 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 66 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 41 146 292 14 81 96 66 133 261), lower := (rows 41 146 292 14 81 96 66 128 256), losses := [] }

theorem u8475 : Upper (D 6) (R 6) [40,144,288,6,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8476 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 113, targets := 2 },{ cop := 4, region := 130, targets := 32 }], pairs := [(0,1),(1,5),(4,1)], upper := (rows 41 146 292 14 81 96 68 131 259), lower := (rows 41 146 292 14 81 96 68 128 256), losses := [] }

theorem u8476 : Upper (D 6) (R 6) [40,144,288,6,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8477 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 113, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 146 292 14 84 96 65 131 259), lower := (rows 41 146 292 14 84 96 65 128 256), losses := [] }

theorem u8477 : Upper (D 6) (R 6) [40,144,288,6,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8478 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 260, targets := 66 },{ cop := 3, region := 80, targets := 1 }], pairs := [(2,1),(2,6),(4,0)], upper := (rows 41 146 292 14 84 96 66 129 257), lower := (rows 41 146 292 14 84 96 66 128 256), losses := [] }

theorem u8478 : Upper (D 6) (R 6) [40,144,288,6,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8479 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 41 146 292 73 84 34 65 134 262), lower := (rows 41 146 292 73 84 34 65 128 256), losses := [] }

theorem u8479 : Upper (D 6) (R 6) [40,144,288,65,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8480 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 66 },{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 41 146 292 73 84 34 66 133 261), lower := (rows 41 146 292 73 84 34 66 128 256), losses := [] }

theorem u8480 : Upper (D 6) (R 6) [40,144,288,65,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8481 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 146 292 73 84 34 68 131 259), lower := (rows 41 146 292 73 84 34 68 128 256), losses := [] }

theorem u8481 : Upper (D 6) (R 6) [40,144,288,65,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8482 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 41 146 292 76 81 34 65 134 262), lower := (rows 41 146 292 76 81 34 65 128 256), losses := [] }

theorem u8482 : Upper (D 6) (R 6) [40,144,288,68,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8483 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 66 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,1),(2,6)], upper := (rows 41 146 292 76 81 34 66 133 261), lower := (rows 41 146 292 76 81 34 66 128 256), losses := [] }

theorem u8483 : Upper (D 6) (R 6) [40,144,288,68,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8484 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 146 292 76 81 34 68 131 259), lower := (rows 41 146 292 76 81 34 68 128 256), losses := [] }

theorem u8484 : Upper (D 6) (R 6) [40,144,288,68,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8485 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 146 324 11 21 96 66 164 292), lower := (rows 41 146 324 11 21 96 66 128 256), losses := [] }

theorem u8485 : Upper (D 6) (R 6) [40,144,320,3,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8486 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 8, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 41 146 324 11 21 96 68 162 290), lower := (rows 41 146 324 11 21 96 68 128 256), losses := [] }

theorem u8486 : Upper (D 6) (R 6) [40,144,320,3,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8487 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 138, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 41 146 324 11 21 96 96 134 262), lower := (rows 41 146 324 11 21 96 96 128 256), losses := [] }

theorem u8487 : Upper (D 6) (R 6) [40,144,320,3,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8488 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 80, targets := 36 },{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 41 146 324 11 81 36 66 164 292), lower := (rows 41 146 324 11 81 36 66 128 256), losses := [] }

theorem u8488 : Upper (D 6) (R 6) [40,144,320,3,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8489 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 8, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 41 146 324 11 81 36 68 162 290), lower := (rows 41 146 324 11 81 36 68 128 256), losses := [] }

theorem u8489 : Upper (D 6) (R 6) [40,144,320,3,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8490 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 146 324 11 81 36 96 134 262), lower := (rows 41 146 324 11 81 36 96 128 256), losses := [] }

theorem u8490 : Upper (D 6) (R 6) [40,144,320,3,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8491 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 146 324 11 82 36 65 164 292), lower := (rows 41 146 324 11 82 36 65 128 256), losses := [] }

theorem u8491 : Upper (D 6) (R 6) [40,144,320,3,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8492 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 8, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 146 324 11 82 36 68 161 289), lower := (rows 41 146 324 11 82 36 68 128 256), losses := [] }

theorem u8492 : Upper (D 6) (R 6) [40,144,320,3,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8493 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 146 324 11 82 36 96 133 261), lower := (rows 41 146 324 11 82 36 96 128 256), losses := [] }

theorem u8493 : Upper (D 6) (R 6) [40,144,320,3,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8494 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 41 146 324 13 81 34 66 164 292), lower := (rows 41 146 324 13 81 34 66 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 17 98 98 128 256), good := (rows 121 242 352 25 113 98 98 128 256) }] }

theorem u8494 : Upper (D 6) (R 6) [40,144,320,5,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8495 : PairBound 9 := { available := 34, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 41 146 324 13 81 34 68 162 290), lower := (rows 41 146 324 13 81 34 68 128 256), losses := [] }

theorem u8495 : Upper (D 6) (R 6) [40,144,320,5,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8496 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 146 324 13 81 34 96 134 262), lower := (rows 41 146 324 13 81 34 96 128 256), losses := [] }

theorem u8496 : Upper (D 6) (R 6) [40,144,320,5,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8497 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 146 324 13 112 34 65 134 262), lower := (rows 41 146 324 13 112 34 65 128 256), losses := [] }

theorem u8497 : Upper (D 6) (R 6) [40,144,320,5,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8498 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 114, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 146 324 13 112 34 66 133 261), lower := (rows 41 146 324 13 112 34 66 128 256), losses := [] }

theorem u8498 : Upper (D 6) (R 6) [40,144,320,5,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8499 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 41 146 324 13 112 34 68 131 259), lower := (rows 41 146 324 13 112 34 68 128 256), losses := [] }

theorem u8499 : Upper (D 6) (R 6) [40,144,320,5,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8500 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 178, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 41 146 324 73 22 36 65 162 290), lower := (rows 41 146 324 73 22 36 65 128 256), losses := [] }

theorem u8500 : Upper (D 6) (R 6) [40,144,320,65,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8501 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 301, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 324 73 22 36 66 161 289), lower := (rows 41 146 324 73 22 36 66 128 256), losses := [] }

theorem u8501 : Upper (D 6) (R 6) [40,144,320,65,6,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8502 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 146 324 73 22 36 96 131 259), lower := (rows 41 146 324 73 22 36 96 128 256), losses := [] }

theorem u8502 : Upper (D 6) (R 6) [40,144,320,65,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8503 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 178, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 41 146 324 73 50 36 65 134 262), lower := (rows 41 146 324 73 50 36 65 128 256), losses := [] }

theorem u8503 : Upper (D 6) (R 6) [40,144,320,65,34,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8504 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 301, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 324 73 50 36 66 133 261), lower := (rows 41 146 324 73 50 36 66 128 256), losses := [] }

theorem u8504 : Upper (D 6) (R 6) [40,144,320,65,34,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8505 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 146, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 146 324 73 50 36 68 131 259), lower := (rows 41 146 324 73 50 36 68 128 256), losses := [] }

theorem u8505 : Upper (D 6) (R 6) [40,144,320,65,34,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8506 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 178, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 41 146 324 73 52 34 65 134 262), lower := (rows 41 146 324 73 52 34 65 128 256), losses := [] }

theorem u8506 : Upper (D 6) (R 6) [40,144,320,65,36,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8507 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 3, region := 260, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 41 146 324 73 52 34 66 133 261), lower := (rows 41 146 324 73 52 34 66 128 256), losses := [] }

theorem u8507 : Upper (D 6) (R 6) [40,144,320,65,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8508 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 41 146 324 73 52 34 68 131 259), lower := (rows 41 146 324 73 52 34 68 128 256), losses := [] }

theorem u8508 : Upper (D 6) (R 6) [40,144,320,65,36,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8509 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 293, targets := 2 },{ cop := 4, region := 72, targets := 4 }], pairs := [(0,1),(2,1),(3,2)], upper := (rows 41 146 324 74 19 36 65 164 292), lower := (rows 41 146 324 74 19 36 65 128 256), losses := [] }

theorem u8509 : Upper (D 6) (R 6) [40,144,320,66,3,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8510 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 146, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 146 324 74 19 36 68 161 289), lower := (rows 41 146 324 74 19 36 68 128 256), losses := [] }

theorem u8510 : Upper (D 6) (R 6) [40,144,320,66,3,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8511 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 293, targets := 2 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 146 324 74 19 36 96 133 261), lower := (rows 41 146 324 74 19 36 96 128 256), losses := [] }

theorem u8511 : Upper (D 6) (R 6) [40,144,320,66,3,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8512 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 162, targets := 65 },{ cop := 3, region := 292, targets := 1 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 41 146 324 74 21 36 65 162 290), lower := (rows 41 146 324 74 21 36 65 128 256), losses := [] }

theorem u8512 : Upper (D 6) (R 6) [40,144,320,66,5,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8513 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 72, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 146 324 74 21 36 66 161 289), lower := (rows 41 146 324 74 21 36 66 128 256), losses := [] }

theorem u8513 : Upper (D 6) (R 6) [40,144,320,66,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8514 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 130, targets := 36 },{ cop := 8, region := 100, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 41 146 324 74 21 36 96 131 259), lower := (rows 41 146 324 74 21 36 96 128 256), losses := [] }

theorem u8514 : Upper (D 6) (R 6) [40,144,320,66,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8515 : Route 9 := (fun mask => (mask,id))

def c8515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8515 : Upper (D 6) (R 6) [40,144,320,66,6,4,1] 13 := by
  apply FastRouting.sound _ _ [40,144,320,66,6,4,1] 13 (by decide) (choices 1) [1,32] r8515 c8515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u655
  · exact u656

def b8516 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 293, targets := 2 },{ cop := 4, region := 104, targets := 1 }], pairs := [(0,1),(2,1),(3,0)], upper := (rows 41 146 324 74 22 36 96 129 257), lower := (rows 41 146 324 74 22 36 96 128 256), losses := [] }

theorem u8516 : Upper (D 6) (R 6) [40,144,320,66,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8517 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 162 324 13 82 48 65 134 262), lower := (rows 41 162 324 13 82 48 65 128 256), losses := [] }

theorem u8517 : Upper (D 6) (R 6) [40,160,320,5,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8517 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8518 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 114, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 41 162 324 13 82 48 66 133 261), lower := (rows 41 162 324 13 82 48 66 128 256), losses := [] }

theorem u8518 : Upper (D 6) (R 6) [40,160,320,5,66,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8518 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8519 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 41 162 324 13 82 48 68 131 259), lower := (rows 41 162 324 13 82 48 68 128 256), losses := [] }

theorem u8519 : Upper (D 6) (R 6) [40,160,320,5,66,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8519 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8519
end Delivery.IrregularNine14.P06
