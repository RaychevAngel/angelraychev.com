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

def b480 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 28 200 304 33 96 133 261), lower := (rows 67 162 28 200 304 33 96 128 256), losses := [] }

theorem u480 : Upper (D 8) (R 8) [66,160,24,192,288,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b481 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 130, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 88 304 33 65 132 388), lower := (rows 67 162 44 88 304 33 65 128 256), losses := [] }

theorem u481 : Upper (D 8) (R 8) [66,160,40,80,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b482 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 162 44 88 304 33 68 129 385), lower := (rows 67 162 44 88 304 33 68 128 256), losses := [] }

theorem u482 : Upper (D 8) (R 8) [66,160,40,80,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b482 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b483 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 316, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 88 304 33 192 133 261), lower := (rows 67 162 44 88 304 33 192 128 256), losses := [] }

theorem u483 : Upper (D 8) (R 8) [66,160,40,80,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b484 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 130, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 88 400 33 65 164 292), lower := (rows 67 162 44 88 400 33 65 128 256), losses := [] }

theorem u484 : Upper (D 8) (R 8) [66,160,40,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b485 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 88 400 33 68 161 289), lower := (rows 67 162 44 88 400 33 68 128 256), losses := [] }

theorem u485 : Upper (D 8) (R 8) [66,160,40,80,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b485 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b486 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 44 88 400 33 96 133 261), lower := (rows 67 162 44 88 400 33 96 128 256), losses := [] }

theorem u486 : Upper (D 8) (R 8) [66,160,40,80,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b487 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 130, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 152 273 96 65 164 292), lower := (rows 67 162 44 152 273 96 65 128 256), losses := [] }

theorem u487 : Upper (D 8) (R 8) [66,160,40,144,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b488 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 152 273 96 68 161 289), lower := (rows 67 162 44 152 273 96 68 128 256), losses := [] }

theorem u488 : Upper (D 8) (R 8) [66,160,40,144,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b488 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b489 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 152 273 96 96 133 261), lower := (rows 67 162 44 152 273 96 96 128 256), losses := [] }

theorem u489 : Upper (D 8) (R 8) [66,160,40,144,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b490 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 162 44 152 304 33 65 196 324), lower := (rows 67 162 44 152 304 33 65 128 256), losses := [] }

theorem u490 : Upper (D 8) (R 8) [66,160,40,144,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b491 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 67 162 44 152 304 33 68 193 321), lower := (rows 67 162 44 152 304 33 68 128 256), losses := [] }

theorem u491 : Upper (D 8) (R 8) [66,160,40,144,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b491 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b492 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 162 44 152 304 96 65 133 261), lower := (rows 67 162 44 152 304 96 65 128 256), losses := [] }

theorem u492 : Upper (D 8) (R 8) [66,160,40,144,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b493 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 67 162 44 152 304 96 68 129 257), lower := (rows 67 162 44 152 304 96 68 128 256), losses := [] }

theorem u493 : Upper (D 8) (R 8) [66,160,40,144,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b493 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b494 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 130, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 152 336 33 65 164 292), lower := (rows 67 162 44 152 336 33 65 128 256), losses := [] }

theorem u494 : Upper (D 8) (R 8) [66,160,40,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b495 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 152 336 33 68 161 289), lower := (rows 67 162 44 152 336 33 68 128 256), losses := [] }

theorem u495 : Upper (D 8) (R 8) [66,160,40,144,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b495 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b496 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 44 152 336 33 96 133 261), lower := (rows 67 162 44 152 336 33 96 128 256), losses := [] }

theorem u496 : Upper (D 8) (R 8) [66,160,40,144,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b497 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 67 162 44 200 273 33 68 176 304), lower := (rows 67 162 44 200 273 33 68 128 256), losses := [] }

theorem u497 : Upper (D 8) (R 8) [66,160,40,192,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b497 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b498 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 67 162 44 200 273 33 80 164 292), lower := (rows 67 162 44 200 273 33 80 128 256), losses := [] }

theorem u498 : Upper (D 8) (R 8) [66,160,40,192,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b498 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b499 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 200 273 33 96 148 276), lower := (rows 67 162 44 200 273 33 96 128 256), losses := [] }

theorem u499 : Upper (D 8) (R 8) [66,160,40,192,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b500 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 402, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 200 276 33 65 176 304), lower := (rows 67 162 44 200 276 33 65 128 256), losses := [] }

theorem u500 : Upper (D 8) (R 8) [66,160,40,192,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b501 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 200 276 33 80 161 289), lower := (rows 67 162 44 200 276 33 80 128 256), losses := [] }

theorem u501 : Upper (D 8) (R 8) [66,160,40,192,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b501 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b502 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 200 276 33 96 145 273), lower := (rows 67 162 44 200 276 33 96 128 256), losses := [] }

theorem u502 : Upper (D 8) (R 8) [66,160,40,192,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b503 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 200 304 33 65 148 276), lower := (rows 67 162 44 200 304 33 65 128 256), losses := [] }

theorem u503 : Upper (D 8) (R 8) [66,160,40,192,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b504 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 67 162 44 200 304 33 68 145 273), lower := (rows 67 162 44 200 304 33 68 128 256), losses := [] }

theorem u504 : Upper (D 8) (R 8) [66,160,40,192,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b504 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b505 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 67 162 44 200 304 33 80 133 261), lower := (rows 67 162 44 200 304 33 80 128 256), losses := [] }

theorem u505 : Upper (D 8) (R 8) [66,160,40,192,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b505 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b506 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 162 44 268 208 33 65 176 304), lower := (rows 67 162 44 268 208 33 65 128 256), losses := [] }

theorem u506 : Upper (D 8) (R 8) [66,160,40,260,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b507 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 268 208 33 80 161 289), lower := (rows 67 162 44 268 208 33 80 128 256), losses := [] }

theorem u507 : Upper (D 8) (R 8) [66,160,40,260,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b507 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b508 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 67 162 44 268 208 33 96 145 273), lower := (rows 67 162 44 268 208 33 96 128 256), losses := [] }

theorem u508 : Upper (D 8) (R 8) [66,160,40,260,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b509 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 162 44 280 208 33 65 164 292), lower := (rows 67 162 44 280 208 33 65 128 256), losses := [] }

theorem u509 : Upper (D 8) (R 8) [66,160,40,272,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b510 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 280 208 33 68 161 289), lower := (rows 67 162 44 280 208 33 68 128 256), losses := [] }

theorem u510 : Upper (D 8) (R 8) [66,160,40,272,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b510 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b511 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 44 280 208 33 96 133 261), lower := (rows 67 162 44 280 208 33 96 128 256), losses := [] }

theorem u511 : Upper (D 8) (R 8) [66,160,40,272,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b512 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 146, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 328 148 33 65 176 304), lower := (rows 67 162 44 328 148 33 65 128 256), losses := [] }

theorem u512 : Upper (D 8) (R 8) [66,160,40,320,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b513 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 328 148 33 80 161 289), lower := (rows 67 162 44 328 148 33 80 128 256), losses := [] }

theorem u513 : Upper (D 8) (R 8) [66,160,40,320,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b513 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b514 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 44 328 148 33 96 145 273), lower := (rows 67 162 44 328 148 33 96 128 256), losses := [] }

theorem u514 : Upper (D 8) (R 8) [66,160,40,320,132,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b515 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 162 44 392 84 33 65 176 304), lower := (rows 67 162 44 392 84 33 65 128 256), losses := [] }

theorem u515 : Upper (D 8) (R 8) [66,160,40,384,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b516 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 392 84 33 80 161 289), lower := (rows 67 162 44 392 84 33 80 128 256), losses := [] }

theorem u516 : Upper (D 8) (R 8) [66,160,40,384,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b516 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b517 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 44 392 84 33 96 145 273), lower := (rows 67 162 44 392 84 33 96 128 256), losses := [] }

theorem u517 : Upper (D 8) (R 8) [66,160,40,384,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b518 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 162 76 152 304 33 65 164 292), lower := (rows 67 162 76 152 304 33 65 128 256), losses := [] }

theorem u518 : Upper (D 8) (R 8) [66,160,72,144,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b519 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 76 152 304 33 68 161 289), lower := (rows 67 162 76 152 304 33 68 128 256), losses := [] }

theorem u519 : Upper (D 8) (R 8) [66,160,72,144,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b519 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b520 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 76 152 304 33 96 133 261), lower := (rows 67 162 76 152 304 33 96 128 256), losses := [] }

theorem u520 : Upper (D 8) (R 8) [66,160,72,144,288,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b521 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 162 76 296 148 33 65 176 304), lower := (rows 67 162 76 296 148 33 65 128 256), losses := [] }

theorem u521 : Upper (D 8) (R 8) [66,160,72,288,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b522 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 76 296 148 33 80 161 289), lower := (rows 67 162 76 296 148 33 80 128 256), losses := [] }

theorem u522 : Upper (D 8) (R 8) [66,160,72,288,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b522 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b523 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 76 296 148 33 96 145 273), lower := (rows 67 162 76 296 148 33 96 128 256), losses := [] }

theorem u523 : Upper (D 8) (R 8) [66,160,72,288,132,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b524 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 37 104 152 160 65 176 304), lower := (rows 67 262 37 104 152 160 65 128 256), losses := [] }

theorem u524 : Upper (D 8) (R 8) [66,260,33,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b525 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 262 37 104 152 160 80 161 289), lower := (rows 67 262 37 104 152 160 80 128 256), losses := [] }

theorem u525 : Upper (D 8) (R 8) [66,260,33,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b525 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b526 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 37 104 152 160 96 145 273), lower := (rows 67 262 37 104 152 160 96 128 256), losses := [] }

theorem u526 : Upper (D 8) (R 8) [66,260,33,96,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b527 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 390, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 164 56 208 33 65 168 296), lower := (rows 67 262 164 56 208 33 65 128 256), losses := [] }

theorem u527 : Upper (D 8) (R 8) [66,260,160,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b528 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 262 164 56 208 33 72 161 289), lower := (rows 67 262 164 56 208 33 72 128 256), losses := [] }

theorem u528 : Upper (D 8) (R 8) [66,260,160,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b528 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b529 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 164 56 208 33 96 137 265), lower := (rows 67 262 164 56 208 33 96 128 256), losses := [] }

theorem u529 : Upper (D 8) (R 8) [66,260,160,48,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b530 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 386, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 13 28 176 96 65 160 416), lower := (rows 67 290 13 28 176 96 65 128 256), losses := [] }

theorem u530 : Upper (D 8) (R 8) [66,288,9,20,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b531 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 28 176 96 96 129 385), lower := (rows 67 290 13 28 176 96 96 128 256), losses := [] }

theorem u531 : Upper (D 8) (R 8) [66,288,9,20,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b532 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 259, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 28 176 96 192 161 289), lower := (rows 67 290 13 28 176 96 192 128 256), losses := [] }

theorem u532 : Upper (D 8) (R 8) [66,288,9,20,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b533 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 44 112 160 65 144 400), lower := (rows 67 290 13 44 112 160 65 128 256), losses := [] }

theorem u533 : Upper (D 8) (R 8) [66,288,9,36,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b534 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 290 13 44 112 160 80 129 385), lower := (rows 67 290 13 44 112 160 80 128 256), losses := [] }

theorem u534 : Upper (D 8) (R 8) [66,288,9,36,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b534 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b535 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 259, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 44 112 160 192 145 273), lower := (rows 67 290 13 44 112 160 192 128 256), losses := [] }

theorem u535 : Upper (D 8) (R 8) [66,288,9,36,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b536 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 44 208 160 65 176 304), lower := (rows 67 290 13 44 208 160 65 128 256), losses := [] }

theorem u536 : Upper (D 8) (R 8) [66,288,9,36,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b537 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 290 13 44 208 160 80 161 289), lower := (rows 67 290 13 44 208 160 80 128 256), losses := [] }

theorem u537 : Upper (D 8) (R 8) [66,288,9,36,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b537 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b538 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 44 208 160 96 145 273), lower := (rows 67 290 13 44 208 160 96 128 256), losses := [] }

theorem u538 : Upper (D 8) (R 8) [66,288,9,36,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b539 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 386, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 13 56 148 96 65 160 416), lower := (rows 67 290 13 56 148 96 65 128 256), losses := [] }

theorem u539 : Upper (D 8) (R 8) [66,288,9,48,132,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u539
end Delivery.IrregularNine14.P08
