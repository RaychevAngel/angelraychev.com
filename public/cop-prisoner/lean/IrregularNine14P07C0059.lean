import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0003

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3540 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 37 200 336 34 66 129 385), lower := (rows 13 50 37 200 336 34 66 128 256), losses := [] }

theorem u3540 : Upper (D 7) (R 7) [12,48,33,192,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3541 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 37 200 336 34 192 131 259), lower := (rows 13 50 37 200 336 34 192 128 256), losses := [] }

theorem u3541 : Upper (D 7) (R 7) [12,48,33,192,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3542 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 429, targets := 2 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 50 37 265 82 160 66 192 448), lower := (rows 13 50 37 265 82 160 66 128 256), losses := [] }

theorem u3542 : Upper (D 7) (R 7) [12,48,33,257,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3543 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(1,6),(4,0),(4,5)], upper := (rows 13 50 37 265 82 160 192 194 322), lower := (rows 13 50 37 265 82 160 192 128 256), losses := [{ target := 6, region := (rows 1 18 4 8 16 224 0 128 256), good := (rows 13 50 37 265 50 160 160 160 256) }] }

theorem u3543 : Upper (D 7) (R 7) [12,48,33,257,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3544 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 82, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 50 37 266 82 160 65 192 448), lower := (rows 13 50 37 266 82 160 65 128 256), losses := [] }

theorem u3544 : Upper (D 7) (R 7) [12,48,33,258,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3545 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 5, region := 82, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 13 50 37 266 82 160 192 193 321), lower := (rows 13 50 37 266 82 160 192 128 256), losses := [] }

theorem u3545 : Upper (D 7) (R 7) [12,48,33,258,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3546 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 82, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 50 37 328 82 160 65 130 386), lower := (rows 13 50 37 328 82 160 65 128 256), losses := [] }

theorem u3546 : Upper (D 7) (R 7) [12,48,33,320,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3547 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 82, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 37 328 82 160 66 129 385), lower := (rows 13 50 37 328 82 160 66 128 256), losses := [] }

theorem u3547 : Upper (D 7) (R 7) [12,48,33,320,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3548 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 82, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 13 50 37 328 82 160 192 131 259), lower := (rows 13 50 37 328 82 160 192 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 224 224 128 256), good := (rows 13 112 101 365 112 224 224 224 256) }] }

theorem u3548 : Upper (D 7) (R 7) [12,48,33,320,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3549 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 50 37 328 208 34 65 130 386), lower := (rows 13 50 37 328 208 34 65 128 256), losses := [] }

theorem u3549 : Upper (D 7) (R 7) [12,48,33,320,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3550 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 34, targets := 129 },{ cop := 4, region := 34, targets := 64 },{ cop := 7, region := 114, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 37 328 208 34 66 129 385), lower := (rows 13 50 37 328 208 34 66 128 256), losses := [] }

theorem u3550 : Upper (D 7) (R 7) [12,48,33,320,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3551 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 37 328 208 34 192 131 259), lower := (rows 13 50 37 328 208 34 192 128 256), losses := [] }

theorem u3551 : Upper (D 7) (R 7) [12,48,33,320,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3552 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 13 50 69 138 82 288 65 160 416), lower := (rows 13 50 69 138 82 288 65 128 256), losses := [] }

theorem u3552 : Upper (D 7) (R 7) [12,48,65,130,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3552 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3553 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 82, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 50 69 138 82 288 96 129 385), lower := (rows 13 50 69 138 82 288 96 128 256), losses := [] }

theorem u3553 : Upper (D 7) (R 7) [12,48,65,130,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3553 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3554 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 13 50 69 138 82 288 192 161 289), lower := (rows 13 50 69 138 82 288 192 128 256), losses := [] }

theorem u3554 : Upper (D 7) (R 7) [12,48,65,130,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3554 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3555 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 13 50 69 138 208 288 65 162 290), lower := (rows 13 50 69 138 208 288 65 128 256), losses := [] }

theorem u3555 : Upper (D 7) (R 7) [12,48,65,130,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3555 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3556 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 13 50 69 138 208 288 66 161 289), lower := (rows 13 50 69 138 208 288 66 128 256), losses := [] }

theorem u3556 : Upper (D 7) (R 7) [12,48,65,130,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3556 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3557 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 357, targets := 128 }], pairs := [(0,7),(2,7),(4,0)], upper := (rows 13 50 69 138 208 288 96 131 259), lower := (rows 13 50 69 138 208 288 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 288 354 128 256), good := (rows 28 114 68 218 208 352 96 128 352) }] }

theorem u3557 : Upper (D 7) (R 7) [12,48,65,130,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3557 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3558 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 50 69 138 273 96 66 160 416), lower := (rows 13 50 69 138 273 96 66 128 256), losses := [] }

theorem u3558 : Upper (D 7) (R 7) [12,48,65,130,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3559 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 69 138 273 96 96 130 386), lower := (rows 13 50 69 138 273 96 96 128 256), losses := [] }

theorem u3559 : Upper (D 7) (R 7) [12,48,65,130,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3560 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 306, targets := 128 },{ cop := 3, region := 69, targets := 2 }], pairs := [(0,1),(1,7),(2,1),(4,7)], upper := (rows 13 50 69 138 273 96 192 162 290), lower := (rows 13 50 69 138 273 96 192 128 256), losses := [] }

theorem u3560 : Upper (D 7) (R 7) [12,48,65,130,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3561 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 138 274 96 65 160 416), lower := (rows 13 50 69 138 274 96 65 128 256), losses := [] }

theorem u3561 : Upper (D 7) (R 7) [12,48,65,130,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3562 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 69 138 274 96 96 129 385), lower := (rows 13 50 69 138 274 96 96 128 256), losses := [] }

theorem u3562 : Upper (D 7) (R 7) [12,48,65,130,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3563 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 306, targets := 128 },{ cop := 3, region := 69, targets := 2 }], pairs := [(0,1),(1,7),(2,1),(4,7)], upper := (rows 13 50 69 138 274 96 192 161 289), lower := (rows 13 50 69 138 274 96 192 128 256), losses := [] }

theorem u3563 : Upper (D 7) (R 7) [12,48,65,130,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3564 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 50 69 138 274 160 65 224 352), lower := (rows 13 50 69 138 274 160 65 128 256), losses := [] }

theorem u3564 : Upper (D 7) (R 7) [12,48,65,130,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3565 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 69 138 274 160 96 193 321), lower := (rows 13 50 69 138 274 160 96 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 24 32 98 0 268), good := (rows 285 114 325 351 338 96 96 0 256) }] }

theorem u3565 : Upper (D 7) (R 7) [12,48,65,130,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3566 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 50 69 138 336 34 65 160 416), lower := (rows 13 50 69 138 336 34 65 128 256), losses := [] }

theorem u3566 : Upper (D 7) (R 7) [12,48,65,130,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3567 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 69 138 336 34 96 129 385), lower := (rows 13 50 69 138 336 34 96 128 256), losses := [] }

theorem u3567 : Upper (D 7) (R 7) [12,48,65,130,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3568 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 50 69 138 336 34 192 161 289), lower := (rows 13 50 69 138 336 34 192 128 256), losses := [] }

theorem u3568 : Upper (D 7) (R 7) [12,48,65,130,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3569 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 50 69 138 336 160 65 162 290), lower := (rows 13 50 69 138 336 160 65 128 256), losses := [] }

theorem u3569 : Upper (D 7) (R 7) [12,48,65,130,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3570 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 50 69 138 336 160 66 161 289), lower := (rows 13 50 69 138 336 160 66 128 256), losses := [] }

theorem u3570 : Upper (D 7) (R 7) [12,48,65,130,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3571 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 69 138 336 160 96 131 259), lower := (rows 13 50 69 138 336 160 96 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 24 32 98 0 264), good := (rows 285 114 69 351 336 96 96 0 256) }] }

theorem u3571 : Upper (D 7) (R 7) [12,48,65,130,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3572 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 138 400 96 65 162 290), lower := (rows 13 50 69 138 400 96 65 128 256), losses := [] }

theorem u3572 : Upper (D 7) (R 7) [12,48,65,130,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3573 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 50 69 138 400 96 66 161 289), lower := (rows 13 50 69 138 400 96 66 128 256), losses := [] }

theorem u3573 : Upper (D 7) (R 7) [12,48,65,130,384,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3574 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 100, targets := 130 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(2,1),(2,7),(3,0)], upper := (rows 13 50 69 138 400 96 96 131 259), lower := (rows 13 50 69 138 400 96 96 128 256), losses := [] }

theorem u3574 : Upper (D 7) (R 7) [12,48,65,130,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3575 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 13 50 69 168 82 288 65 130 386), lower := (rows 13 50 69 168 82 288 65 128 256), losses := [] }

theorem u3575 : Upper (D 7) (R 7) [12,48,65,160,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3575 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3576 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 13 50 69 168 82 288 66 129 385), lower := (rows 13 50 69 168 82 288 66 128 256), losses := [] }

theorem u3576 : Upper (D 7) (R 7) [12,48,65,160,66,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3576 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3577 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 13 50 69 168 82 288 192 131 259), lower := (rows 13 50 69 168 82 288 192 128 256), losses := [] }

theorem u3577 : Upper (D 7) (R 7) [12,48,65,160,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3577 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3578 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 13 50 69 168 208 288 65 130 258), lower := (rows 13 50 69 168 208 288 65 128 256), losses := [] }

theorem u3578 : Upper (D 7) (R 7) [12,48,65,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3578 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3579 : Route 9 := (fun mask => (mask,id))

def c3579 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3579 : Upper (D 7) (R 7) [12,48,65,160,192,256,2] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,192,256,2] 13 (by decide) (choices 1) [1,2] r3579 c3579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u220
  · exact u221

def b3580 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 50 69 168 273 96 66 130 386), lower := (rows 13 50 69 168 273 96 66 128 256), losses := [] }

theorem u3580 : Upper (D 7) (R 7) [12,48,65,160,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3581 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 45, targets := 2 },{ cop := 2, region := 306, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(3,1)], upper := (rows 13 50 69 168 273 96 192 130 258), lower := (rows 13 50 69 168 273 96 192 128 256), losses := [] }

theorem u3581 : Upper (D 7) (R 7) [12,48,65,160,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3582 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 168 274 96 65 130 386), lower := (rows 13 50 69 168 274 96 65 128 256), losses := [] }

theorem u3582 : Upper (D 7) (R 7) [12,48,65,160,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3583 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 69 168 274 96 66 129 385), lower := (rows 13 50 69 168 274 96 66 128 256), losses := [] }

theorem u3583 : Upper (D 7) (R 7) [12,48,65,160,258,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3584 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 45, targets := 2 },{ cop := 2, region := 306, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(3,1)], upper := (rows 13 50 69 168 274 96 192 131 259), lower := (rows 13 50 69 168 274 96 192 128 256), losses := [] }

theorem u3584 : Upper (D 7) (R 7) [12,48,65,160,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3585 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 50 69 168 336 34 65 130 386), lower := (rows 13 50 69 168 336 34 65 128 256), losses := [] }

theorem u3585 : Upper (D 7) (R 7) [12,48,65,160,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3586 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 69 168 336 34 66 129 385), lower := (rows 13 50 69 168 336 34 66 128 256), losses := [] }

theorem u3586 : Upper (D 7) (R 7) [12,48,65,160,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3587 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 50 69 168 336 34 192 131 259), lower := (rows 13 50 69 168 336 34 192 128 256), losses := [] }

theorem u3587 : Upper (D 7) (R 7) [12,48,65,160,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3588 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 168 400 96 65 130 258), lower := (rows 13 50 69 168 400 96 65 128 256), losses := [] }

theorem u3588 : Upper (D 7) (R 7) [12,48,65,160,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3589 : Route 9 := (fun mask => (mask,id))

def c3589 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3589 : Upper (D 7) (R 7) [12,48,65,160,384,64,2] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160,384,64,2] 13 (by decide) (choices 1) [1,2] r3589 c3589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u222
  · exact u223

def b3590 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 50 69 265 82 160 66 160 416), lower := (rows 13 50 69 265 82 160 66 128 256), losses := [] }

theorem u3590 : Upper (D 7) (R 7) [12,48,65,257,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3591 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 265 82 160 96 130 386), lower := (rows 13 50 69 265 82 160 96 128 256), losses := [] }

theorem u3591 : Upper (D 7) (R 7) [12,48,65,257,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3592 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,5)], upper := (rows 13 50 69 265 82 160 192 162 290), lower := (rows 13 50 69 265 82 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 18 0 224 128 256), good := (rows 13 82 69 265 82 192 192 192 256) }] }

theorem u3592 : Upper (D 7) (R 7) [12,48,65,257,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3593 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 50 69 266 82 160 65 160 416), lower := (rows 13 50 69 266 82 160 65 128 256), losses := [] }

theorem u3593 : Upper (D 7) (R 7) [12,48,65,258,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3594 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 82, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 69 266 82 160 96 129 385), lower := (rows 13 50 69 266 82 160 96 128 256), losses := [] }

theorem u3594 : Upper (D 7) (R 7) [12,48,65,258,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3595 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 5, region := 82, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 13 50 69 266 82 160 192 161 289), lower := (rows 13 50 69 266 82 160 192 128 256), losses := [] }

theorem u3595 : Upper (D 7) (R 7) [12,48,65,258,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3596 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 50 69 266 145 96 66 160 416), lower := (rows 13 50 69 266 145 96 66 128 256), losses := [] }

theorem u3596 : Upper (D 7) (R 7) [12,48,65,258,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3597 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 69 266 145 96 96 130 386), lower := (rows 13 50 69 266 145 96 96 128 256), losses := [] }

theorem u3597 : Upper (D 7) (R 7) [12,48,65,258,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3598 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 1, region := 264, targets := 64 },{ cop := 1, region := 264, targets := 128 }], pairs := [(1,0),(3,0),(3,6),(3,7)], upper := (rows 13 50 69 266 145 96 192 162 290), lower := (rows 13 50 69 266 145 96 192 128 256), losses := [] }

theorem u3598 : Upper (D 7) (R 7) [12,48,65,258,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3599 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 69 266 146 96 65 160 416), lower := (rows 13 50 69 266 146 96 65 128 256), losses := [] }

theorem u3599 : Upper (D 7) (R 7) [12,48,65,258,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3599
end Delivery.IrregularNine14.P07
