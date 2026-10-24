import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3420 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 35 70 266 208 160 96 145 273), lower := (rows 13 35 70 266 208 160 96 128 256), losses := [] }

theorem u3420 : Upper (D 7) (R 7) [12,33,66,258,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3421 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 84, targets := 160 }], pairs := [(2,5),(2,7),(4,5),(4,7)], upper := (rows 13 35 70 280 81 160 66 160 416), lower := (rows 13 35 70 280 81 160 66 128 256), losses := [] }

theorem u3421 : Upper (D 7) (R 7) [12,33,66,272,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3422 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 128 }], pairs := [(0,5),(2,7),(3,5),(4,5)], upper := (rows 13 35 70 280 81 160 96 130 386), lower := (rows 13 35 70 280 81 160 96 128 256), losses := [] }

theorem u3422 : Upper (D 7) (R 7) [12,33,66,272,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3423 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,6),(2,0),(3,6),(4,1)], upper := (rows 13 35 70 280 81 160 192 162 290), lower := (rows 13 35 70 280 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 18 224 224 128 256), good := (rows 13 113 116 280 113 224 224 224 256) }] }

theorem u3423 : Upper (D 7) (R 7) [12,33,66,272,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3424 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 84, targets := 128 },{ cop := 2, region := 440, targets := 1 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 70 280 112 160 65 130 386), lower := (rows 13 35 70 280 112 160 65 128 256), losses := [] }

theorem u3424 : Upper (D 7) (R 7) [12,33,66,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3425 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 35 70 280 112 160 66 129 385), lower := (rows 13 35 70 280 112 160 66 128 256), losses := [] }

theorem u3425 : Upper (D 7) (R 7) [12,33,66,272,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3426 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 70 280 112 160 192 131 259), lower := (rows 13 35 70 280 112 160 192 128 256), losses := [] }

theorem u3426 : Upper (D 7) (R 7) [12,33,66,272,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3427 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 6, region := 4, targets := 32 }], pairs := [(0,1),(2,5),(3,1),(4,1)], upper := (rows 13 35 70 280 145 160 66 224 352), lower := (rows 13 35 70 280 145 160 66 128 256), losses := [] }

theorem u3427 : Upper (D 7) (R 7) [12,33,66,272,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3428 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,5),(2,0),(3,5),(4,5)], upper := (rows 13 35 70 280 145 160 96 194 322), lower := (rows 13 35 70 280 145 160 96 128 256), losses := [] }

theorem u3428 : Upper (D 7) (R 7) [12,33,66,272,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3429 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 440, targets := 1 },{ cop := 0, region := 162, targets := 64 },{ cop := 1, region := 68, targets := 32 }], pairs := [(1,6),(2,5),(3,0),(4,0)], upper := (rows 13 35 70 280 208 160 65 162 290), lower := (rows 13 35 70 280 208 160 65 128 256), losses := [] }

theorem u3429 : Upper (D 7) (R 7) [12,33,66,272,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3430 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 13 35 70 280 208 160 66 161 289), lower := (rows 13 35 70 280 208 160 66 128 256), losses := [] }

theorem u3430 : Upper (D 7) (R 7) [12,33,66,272,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3431 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 5, region := 80, targets := 1 }], pairs := [(0,5),(3,5),(4,0),(4,5)], upper := (rows 13 35 70 280 208 160 96 131 259), lower := (rows 13 35 70 280 208 160 96 128 256), losses := [] }

theorem u3431 : Upper (D 7) (R 7) [12,33,66,272,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3432 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 3, region := 71, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 13 35 70 296 145 160 66 208 336), lower := (rows 13 35 70 296 145 160 66 128 256), losses := [] }

theorem u3432 : Upper (D 7) (R 7) [12,33,66,288,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3433 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 2, region := 424, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 13 35 70 296 145 160 80 194 322), lower := (rows 13 35 70 296 145 160 80 128 256), losses := [] }

theorem u3433 : Upper (D 7) (R 7) [12,33,66,288,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3433 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3434 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 1, region := 68, targets := 32 }], pairs := [(0,7),(1,7),(2,5),(2,7)], upper := (rows 13 35 70 296 146 160 65 208 336), lower := (rows 13 35 70 296 146 160 65 128 256), losses := [] }

theorem u3434 : Upper (D 7) (R 7) [12,33,66,288,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3435 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(2,5),(4,5)], upper := (rows 13 35 70 296 146 160 80 193 321), lower := (rows 13 35 70 296 146 160 80 128 256), losses := [] }

theorem u3435 : Upper (D 7) (R 7) [12,33,66,288,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3435 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3436 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 1, region := 68, targets := 32 }], pairs := [(0,7),(1,7),(2,5),(2,7)], upper := (rows 13 35 70 296 208 160 65 146 274), lower := (rows 13 35 70 296 208 160 65 128 256), losses := [] }

theorem u3436 : Upper (D 7) (R 7) [12,33,66,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3437 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 3, region := 71, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 13 35 70 296 208 160 66 145 273), lower := (rows 13 35 70 296 208 160 66 128 256), losses := [] }

theorem u3437 : Upper (D 7) (R 7) [12,33,66,288,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3438 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 70 296 208 160 80 131 259), lower := (rows 13 35 70 296 208 160 80 128 256), losses := [] }

theorem u3438 : Upper (D 7) (R 7) [12,33,66,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3438 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3439 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 35 70 328 145 160 66 176 304), lower := (rows 13 35 70 328 145 160 66 128 256), losses := [] }

theorem u3439 : Upper (D 7) (R 7) [12,33,66,320,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3440 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 2, region := 424, targets := 1 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 13 35 70 328 145 160 80 162 290), lower := (rows 13 35 70 328 145 160 80 128 256), losses := [] }

theorem u3440 : Upper (D 7) (R 7) [12,33,66,320,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3440 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3441 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 0, region := 178, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 35 70 328 145 160 96 146 274), lower := (rows 13 35 70 328 145 160 96 128 256), losses := [] }

theorem u3441 : Upper (D 7) (R 7) [12,33,66,320,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3442 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 68, targets := 160 }], pairs := [(1,6),(2,5),(2,7),(4,6)], upper := (rows 13 35 70 328 146 160 65 176 304), lower := (rows 13 35 70 328 146 160 65 128 256), losses := [] }

theorem u3442 : Upper (D 7) (R 7) [12,33,66,320,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3443 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(1,6),(4,6)], upper := (rows 13 35 70 328 146 160 80 161 289), lower := (rows 13 35 70 328 146 160 80 128 256), losses := [] }

theorem u3443 : Upper (D 7) (R 7) [12,33,66,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3443 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3444 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 409, targets := 32 },{ cop := 0, region := 178, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 35 70 328 146 160 96 145 273), lower := (rows 13 35 70 328 146 160 96 128 256), losses := [] }

theorem u3444 : Upper (D 7) (R 7) [12,33,66,320,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3445 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 84, targets := 128 },{ cop := 2, region := 440, targets := 1 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 70 392 112 160 65 146 274), lower := (rows 13 35 70 392 112 160 65 128 256), losses := [] }

theorem u3445 : Upper (D 7) (R 7) [12,33,66,384,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3446 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 13 35 70 392 112 160 66 145 273), lower := (rows 13 35 70 392 112 160 66 128 256), losses := [] }

theorem u3446 : Upper (D 7) (R 7) [12,33,66,384,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3447 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 70 392 112 160 80 131 259), lower := (rows 13 35 70 392 112 160 80 128 256), losses := [] }

theorem u3447 : Upper (D 7) (R 7) [12,33,66,384,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3447 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3448 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 77, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 35 84 200 400 34 65 162 290), lower := (rows 13 35 84 200 400 34 65 128 256), losses := [] }

theorem u3448 : Upper (D 7) (R 7) [12,33,80,192,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3449 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 400, targets := 2 }], pairs := [(1,6),(1,7),(4,1),(4,6)], upper := (rows 13 35 84 200 400 34 66 161 289), lower := (rows 13 35 84 200 400 34 66 128 256), losses := [] }

theorem u3449 : Upper (D 7) (R 7) [12,33,80,192,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3450 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,6),(1,7),(4,5),(4,6)], upper := (rows 13 35 84 200 400 34 96 131 259), lower := (rows 13 35 84 200 400 34 96 128 256), losses := [] }

theorem u3450 : Upper (D 7) (R 7) [12,33,80,192,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3451 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 328, targets := 1 },{ cop := 1, region := 328, targets := 128 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,7),(4,1)], upper := (rows 13 35 84 266 145 160 66 224 352), lower := (rows 13 35 84 266 145 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 245 64 196 324), good := (rows 445 49 500 264 177 160 480 160 256) }] }

theorem u3451 : Upper (D 7) (R 7) [12,33,80,258,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3452 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 100, targets := 3 },{ cop := 1, region := 328, targets := 1 },{ cop := 1, region := 328, targets := 128 }], pairs := [(2,0),(2,1),(3,0),(3,7)], upper := (rows 13 35 84 266 145 160 96 194 322), lower := (rows 13 35 84 266 145 160 96 128 256), losses := [] }

theorem u3452 : Upper (D 7) (R 7) [12,33,80,258,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3453 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 456, targets := 32 }], pairs := [(0,5),(1,6),(1,7),(3,5)], upper := (rows 13 35 84 392 176 34 65 194 322), lower := (rows 13 35 84 392 176 34 65 128 256), losses := [{ target := 5, region := (rows 21 2 20 58 16 0 87 162 290), good := (rows 77 459 93 392 477 458 65 128 256) }] }

theorem u3453 : Upper (D 7) (R 7) [12,33,80,384,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3454 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 393, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 35 84 392 176 34 66 193 321), lower := (rows 13 35 84 392 176 34 66 128 256), losses := [] }

theorem u3454 : Upper (D 7) (R 7) [12,33,80,384,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3455 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 84, targets := 128 }], pairs := [(2,7),(3,5),(4,5),(4,7)], upper := (rows 13 35 100 266 82 160 65 144 400), lower := (rows 13 35 100 266 82 160 65 128 256), losses := [] }

theorem u3455 : Upper (D 7) (R 7) [12,33,96,258,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3456 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0)], upper := (rows 13 35 100 266 82 160 80 129 385), lower := (rows 13 35 100 266 82 160 80 128 256), losses := [] }

theorem u3456 : Upper (D 7) (R 7) [12,33,96,258,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3456 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3457 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 35 100 266 82 160 192 145 273), lower := (rows 13 35 100 266 82 160 192 128 256), losses := [] }

theorem u3457 : Upper (D 7) (R 7) [12,33,96,258,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3458 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 68, targets := 129 },{ cop := 1, region := 472, targets := 32 }], pairs := [(2,0),(2,7),(3,5),(4,5)], upper := (rows 13 35 100 266 145 160 66 208 336), lower := (rows 13 35 100 266 145 160 66 128 256), losses := [] }

theorem u3458 : Upper (D 7) (R 7) [12,33,96,258,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3459 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 13 35 100 266 145 160 80 194 322), lower := (rows 13 35 100 266 145 160 80 128 256), losses := [] }

theorem u3459 : Upper (D 7) (R 7) [12,33,96,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3459 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3460 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 68, targets := 2 },{ cop := 1, region := 68, targets := 128 }], pairs := [(2,1),(2,7),(3,5),(4,5)], upper := (rows 13 35 100 266 146 160 65 208 336), lower := (rows 13 35 100 266 146 160 65 128 256), losses := [] }

theorem u3460 : Upper (D 7) (R 7) [12,33,96,258,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3461 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 13 35 100 266 146 160 80 193 321), lower := (rows 13 35 100 266 146 160 80 128 256), losses := [] }

theorem u3461 : Upper (D 7) (R 7) [12,33,96,258,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3461 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3462 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0),(3,0),(3,7),(4,7)], upper := (rows 13 35 196 266 82 160 65 176 304), lower := (rows 13 35 196 266 82 160 65 128 256), losses := [] }

theorem u3462 : Upper (D 7) (R 7) [12,33,192,258,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3463 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 196 266 82 160 80 161 289), lower := (rows 13 35 196 266 82 160 80 128 256), losses := [] }

theorem u3463 : Upper (D 7) (R 7) [12,33,192,258,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3463 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3464 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,5),(2,5),(3,5),(3,7)], upper := (rows 13 35 196 266 82 160 96 145 273), lower := (rows 13 35 196 266 82 160 96 128 256), losses := [] }

theorem u3464 : Upper (D 7) (R 7) [12,33,192,258,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3465 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 0, region := 34, targets := 64 },{ cop := 1, region := 80, targets := 2 }], pairs := [(1,6),(1,7),(4,1),(4,7)], upper := (rows 13 35 196 280 112 34 65 130 386), lower := (rows 13 35 196 280 112 34 65 128 256), losses := [] }

theorem u3465 : Upper (D 7) (R 7) [12,33,192,272,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3466 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 397, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 35 196 280 112 34 66 129 385), lower := (rows 13 35 196 280 112 34 66 128 256), losses := [] }

theorem u3466 : Upper (D 7) (R 7) [12,33,192,272,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3467 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 35 196 280 112 34 192 131 259), lower := (rows 13 35 196 280 112 34 192 128 256), losses := [] }

theorem u3467 : Upper (D 7) (R 7) [12,33,192,272,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3468 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 144, targets := 1 }], pairs := [(1,6),(1,7),(4,0),(4,6)], upper := (rows 13 35 196 328 146 34 65 176 304), lower := (rows 13 35 196 328 146 34 65 128 256), losses := [] }

theorem u3468 : Upper (D 7) (R 7) [12,33,192,320,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3469 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 13 35 196 328 146 34 80 161 289), lower := (rows 13 35 196 328 146 34 80 128 256), losses := [] }

theorem u3469 : Upper (D 7) (R 7) [12,33,192,320,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3469 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3470 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,6),(1,7),(4,5),(4,6)], upper := (rows 13 35 196 328 146 34 96 145 273), lower := (rows 13 35 196 328 146 34 96 128 256), losses := [] }

theorem u3470 : Upper (D 7) (R 7) [12,33,192,320,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3471 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 144, targets := 1 }], pairs := [(1,6),(1,7),(4,0),(4,6)], upper := (rows 13 35 196 328 176 34 65 146 274), lower := (rows 13 35 196 328 176 34 65 128 256), losses := [] }

theorem u3471 : Upper (D 7) (R 7) [12,33,192,320,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3472 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 144, targets := 2 }], pairs := [(1,6),(1,7),(4,1),(4,6)], upper := (rows 13 35 196 328 176 34 66 145 273), lower := (rows 13 35 196 328 176 34 66 128 256), losses := [] }

theorem u3472 : Upper (D 7) (R 7) [12,33,192,320,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3473 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 13 35 196 328 176 34 80 131 259), lower := (rows 13 35 196 328 176 34 80 128 256), losses := [] }

theorem u3473 : Upper (D 7) (R 7) [12,33,192,320,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3473 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3474 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 50 7 73 336 160 66 160 416), lower := (rows 13 50 7 73 336 160 66 128 256), losses := [] }

theorem u3474 : Upper (D 7) (R 7) [12,48,3,65,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3475 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 7 73 336 160 96 130 386), lower := (rows 13 50 7 73 336 160 96 128 256), losses := [] }

theorem u3475 : Upper (D 7) (R 7) [12,48,3,65,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3476 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(0,5),(1,0),(1,6),(4,0)], upper := (rows 13 50 7 73 336 160 192 162 290), lower := (rows 13 50 7 73 336 160 192 128 256), losses := [{ target := 5, region := (rows 7 2 6 10 16 0 224 128 256), good := (rows 13 95 15 73 336 192 192 192 256) }] }

theorem u3476 : Upper (D 7) (R 7) [12,48,3,65,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3477 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 50 7 104 208 288 65 130 386), lower := (rows 13 50 7 104 208 288 65 128 256), losses := [] }

theorem u3477 : Upper (D 7) (R 7) [12,48,3,96,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3477 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3478 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 50 7 104 208 288 66 129 385), lower := (rows 13 50 7 104 208 288 66 128 256), losses := [] }

theorem u3478 : Upper (D 7) (R 7) [12,48,3,96,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3478 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3479 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 50 7 104 208 288 192 131 259), lower := (rows 13 50 7 104 208 288 192 128 256), losses := [] }

theorem u3479 : Upper (D 7) (R 7) [12,48,3,96,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3479 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3479
end Delivery.IrregularNine14.P07
