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

def b480 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 13 274 96 80 160 260), lower := (rows 35 131 76 13 274 96 80 160 256), losses := [] }

theorem u480 : Upper (D 6) (R 6) [34,129,72,5,258,64,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b480 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b481 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 14 273 96 80 132 288), lower := (rows 35 131 76 14 273 96 80 132 256), losses := [] }

theorem u481 : Upper (D 6) (R 6) [34,129,72,6,257,64,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b481 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b482 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 14 273 96 80 160 260), lower := (rows 35 131 76 14 273 96 80 160 256), losses := [] }

theorem u482 : Upper (D 6) (R 6) [34,129,72,6,257,64,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b482 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b483 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 284, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 28 304 96 66 129 260), lower := (rows 35 131 76 28 304 96 66 129 256), losses := [] }

theorem u483 : Upper (D 6) (R 6) [34,129,72,20,288,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b484 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 371, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 28 304 96 66 132 257), lower := (rows 35 131 76 28 304 96 66 132 256), losses := [] }

theorem u484 : Upper (D 6) (R 6) [34,129,72,20,288,64,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b485 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 131 76 56 273 36 66 132 320), lower := (rows 35 131 76 56 273 36 66 132 256), losses := [] }

theorem u485 : Upper (D 6) (R 6) [34,129,72,48,257,4,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b486 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 194, targets := 36 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 131 76 56 273 36 66 192 260), lower := (rows 35 131 76 56 273 36 66 192 256), losses := [] }

theorem u486 : Upper (D 6) (R 6) [34,129,72,48,257,4,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b487 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 131 76 56 274 36 65 132 320), lower := (rows 35 131 76 56 274 36 65 132 256), losses := [] }

theorem u487 : Upper (D 6) (R 6) [34,129,72,48,258,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b488 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 194, targets := 36 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 131 76 56 274 36 65 192 260), lower := (rows 35 131 76 56 274 36 65 192 256), losses := [] }

theorem u488 : Upper (D 6) (R 6) [34,129,72,48,258,4,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b489 : PairBound 9 := { available := 64, camps := [{ cop := 7, region := 3, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 265 22 36 80 160 320), lower := (rows 35 131 76 265 22 36 80 160 256), losses := [] }

theorem u489 : Upper (D 6) (R 6) [34,129,72,257,6,4,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b489 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b490 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 264, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 131 76 265 22 36 80 192 288), lower := (rows 35 131 76 265 22 36 80 192 256), losses := [] }

theorem u490 : Upper (D 6) (R 6) [34,129,72,257,6,4,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b490 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b491 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 264, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 131 76 265 22 96 80 132 288), lower := (rows 35 131 76 265 22 96 80 132 256), losses := [] }

theorem u491 : Upper (D 6) (R 6) [34,129,72,257,6,64,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b491 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b492 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 265 22 96 80 160 260), lower := (rows 35 131 76 265 22 96 80 160 256), losses := [] }

theorem u492 : Upper (D 6) (R 6) [34,129,72,257,6,64,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b492 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b493 : PairBound 9 := { available := 64, camps := [{ cop := 7, region := 3, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 266 21 36 80 160 320), lower := (rows 35 131 76 266 21 36 80 160 256), losses := [] }

theorem u493 : Upper (D 6) (R 6) [34,129,72,258,5,4,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b493 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b494 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 35 131 76 266 21 36 80 192 288), lower := (rows 35 131 76 266 21 36 80 192 256), losses := [] }

theorem u494 : Upper (D 6) (R 6) [34,129,72,258,5,4,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b494 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b495 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 35 131 76 266 21 96 80 132 288), lower := (rows 35 131 76 266 21 96 80 132 256), losses := [] }

theorem u495 : Upper (D 6) (R 6) [34,129,72,258,5,64,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b495 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b496 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 266 21 96 80 160 260), lower := (rows 35 131 76 266 21 96 80 160 256), losses := [] }

theorem u496 : Upper (D 6) (R 6) [34,129,72,258,5,64,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b496 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b497 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 296 22 96 80 129 260), lower := (rows 35 131 76 296 22 96 80 129 256), losses := [] }

theorem u497 : Upper (D 6) (R 6) [34,129,72,288,6,64,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b497 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b498 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 264, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 131 76 296 22 96 80 132 257), lower := (rows 35 131 76 296 22 96 80 132 256), losses := [] }

theorem u498 : Upper (D 6) (R 6) [34,129,72,288,6,64,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b498 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b499 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 261 14 56 96 68 144 320), lower := (rows 35 131 261 14 56 96 68 144 256), losses := [] }

theorem u499 : Upper (D 6) (R 6) [34,129,257,6,40,64,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b499 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b500 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 131 261 14 56 96 68 192 272), lower := (rows 35 131 261 14 56 96 68 192 256), losses := [] }

theorem u500 : Upper (D 6) (R 6) [34,129,257,6,40,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b501 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 139, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 261 26 52 96 68 136 320), lower := (rows 35 131 261 26 52 96 68 136 256), losses := [] }

theorem u501 : Upper (D 6) (R 6) [34,129,257,18,36,64,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b501 [(7,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b502 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 131 261 26 52 96 68 192 264), lower := (rows 35 131 261 26 52 96 68 192 256), losses := [] }

theorem u502 : Upper (D 6) (R 6) [34,129,257,18,36,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b503 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 261 26 52 96 72 132 320), lower := (rows 35 131 261 26 52 96 72 132 256), losses := [] }

theorem u503 : Upper (D 6) (R 6) [34,129,257,18,36,64,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b503 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b504 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 131 261 26 52 96 72 192 260), lower := (rows 35 131 261 26 52 96 72 192 256), losses := [] }

theorem u504 : Upper (D 6) (R 6) [34,129,257,18,36,64,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b504 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b505 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 131 261 28 82 96 68 136 288), lower := (rows 35 131 261 28 82 96 68 136 256), losses := [] }

theorem u505 : Upper (D 6) (R 6) [34,129,257,20,66,64,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b505 [(7,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b506 : PairBound 9 := { available := 8, camps := [{ cop := 7, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 261 28 82 96 68 160 264), lower := (rows 35 131 261 28 82 96 68 160 256), losses := [] }

theorem u506 : Upper (D 6) (R 6) [34,129,257,20,66,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b507 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 262 13 56 96 68 144 320), lower := (rows 35 131 262 13 56 96 68 144 256), losses := [] }

theorem u507 : Upper (D 6) (R 6) [34,129,258,5,40,64,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b507 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b508 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 131 262 13 56 96 68 192 272), lower := (rows 35 131 262 13 56 96 68 192 256), losses := [] }

theorem u508 : Upper (D 6) (R 6) [34,129,258,5,40,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b509 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 262 28 81 36 72 160 320), lower := (rows 35 131 262 28 81 36 72 160 256), losses := [] }

theorem u509 : Upper (D 6) (R 6) [34,129,258,20,65,4,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b509 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b510 : PairBound 9 := { available := 32, camps := [{ cop := 7, region := 295, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 262 28 81 36 72 192 288), lower := (rows 35 131 262 28 81 36 72 192 256), losses := [] }

theorem u510 : Upper (D 6) (R 6) [34,129,258,20,65,4,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b510 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b511 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 260, targets := 1 },{ cop := 0, region := 260, targets := 64 }], pairs := [(2,0),(2,6)], upper := (rows 35 131 262 28 81 96 68 136 288), lower := (rows 35 131 262 28 81 96 68 136 256), losses := [] }

theorem u511 : Upper (D 6) (R 6) [34,129,258,20,65,64,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b511 [(7,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b512 : PairBound 9 := { available := 8, camps := [{ cop := 7, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 262 28 81 96 68 160 264), lower := (rows 35 131 262 28 81 96 68 160 256), losses := [] }

theorem u512 : Upper (D 6) (R 6) [34,129,258,20,65,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b513 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 262 44 81 96 68 136 272), lower := (rows 35 131 262 44 81 96 68 136 256), losses := [] }

theorem u513 : Upper (D 6) (R 6) [34,129,258,36,65,64,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b513 [(7,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b514 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 147, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 262 44 81 96 68 144 264), lower := (rows 35 131 262 44 81 96 68 144 256), losses := [] }

theorem u514 : Upper (D 6) (R 6) [34,129,258,36,65,64,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b514 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b515 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 146, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 35 131 268 13 22 96 96 144 320), lower := (rows 35 131 268 13 22 96 96 144 256), losses := [] }

theorem u515 : Upper (D 6) (R 6) [34,129,264,5,6,64,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b515 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b516 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 284, targets := 96 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 35 131 268 13 22 96 96 192 272), lower := (rows 35 131 268 13 22 96 96 192 256), losses := [] }

theorem u516 : Upper (D 6) (R 6) [34,129,264,5,6,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b517 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 130, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 35 131 268 14 21 96 96 144 320), lower := (rows 35 131 268 14 21 96 96 144 256), losses := [] }

theorem u517 : Upper (D 6) (R 6) [34,129,264,6,5,64,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b517 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b518 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 284, targets := 96 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 35 131 268 14 21 96 96 192 272), lower := (rows 35 131 268 14 21 96 96 192 256), losses := [] }

theorem u518 : Upper (D 6) (R 6) [34,129,264,6,5,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b519 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 268 73 22 96 68 144 288), lower := (rows 35 131 268 73 22 96 68 144 256), losses := [] }

theorem u519 : Upper (D 6) (R 6) [34,129,264,65,6,64,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b519 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b520 : PairBound 9 := { available := 16, camps := [{ cop := 7, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 73 22 96 68 160 272), lower := (rows 35 131 268 73 22 96 68 160 256), losses := [] }

theorem u520 : Upper (D 6) (R 6) [34,129,264,65,6,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b521 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 268 74 21 96 68 144 288), lower := (rows 35 131 268 74 21 96 68 144 256), losses := [] }

theorem u521 : Upper (D 6) (R 6) [34,129,264,66,5,64,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b521 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b522 : PairBound 9 := { available := 16, camps := [{ cop := 7, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 74 21 96 68 160 272), lower := (rows 35 131 268 74 21 96 68 160 256), losses := [] }

theorem u522 : Upper (D 6) (R 6) [34,129,264,66,5,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b523 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 292 14 81 96 68 136 272), lower := (rows 35 131 292 14 81 96 68 136 256), losses := [] }

theorem u523 : Upper (D 6) (R 6) [34,129,288,6,65,64,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b523 [(7,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b524 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 147, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 292 14 81 96 68 144 264), lower := (rows 35 131 292 14 81 96 68 144 256), losses := [] }

theorem u524 : Upper (D 6) (R 6) [34,129,288,6,65,64,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b524 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b525 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 377, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 134 44 26 273 96 65 132 320), lower := (rows 35 134 44 26 273 96 65 132 256), losses := [] }

theorem u525 : Upper (D 6) (R 6) [34,132,40,18,257,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b526 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 134 44 26 273 96 65 192 260), lower := (rows 35 134 44 26 273 96 65 192 256), losses := [] }

theorem u526 : Upper (D 6) (R 6) [34,132,40,18,257,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b527 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 131, targets := 64 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 44 26 276 96 65 129 320), lower := (rows 35 134 44 26 276 96 65 129 256), losses := [] }

theorem u527 : Upper (D 6) (R 6) [34,132,40,18,260,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b528 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 134 44 26 276 96 65 192 257), lower := (rows 35 134 44 26 276 96 65 192 256), losses := [] }

theorem u528 : Upper (D 6) (R 6) [34,132,40,18,260,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b529 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 131, targets := 64 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 44 266 84 96 65 129 272), lower := (rows 35 134 44 266 84 96 65 129 256), losses := [] }

theorem u529 : Upper (D 6) (R 6) [34,132,40,258,68,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b530 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 134 44 266 84 96 65 144 257), lower := (rows 35 134 44 266 84 96 65 144 256), losses := [] }

theorem u530 : Upper (D 6) (R 6) [34,132,40,258,68,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b530 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b531 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 348, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 134 76 26 276 33 96 129 320), lower := (rows 35 134 76 26 276 33 96 129 256), losses := [] }

theorem u531 : Upper (D 6) (R 6) [34,132,72,18,260,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b532 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 134 76 26 276 33 96 192 257), lower := (rows 35 134 76 26 276 33 96 192 256), losses := [] }

theorem u532 : Upper (D 6) (R 6) [34,132,72,18,260,1,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b533 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 134 76 26 276 96 65 129 288), lower := (rows 35 134 76 26 276 96 65 129 256), losses := [] }

theorem u533 : Upper (D 6) (R 6) [34,132,72,18,260,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b534 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 134 76 26 276 96 65 160 257), lower := (rows 35 134 76 26 276 96 65 160 256), losses := [] }

theorem u534 : Upper (D 6) (R 6) [34,132,72,18,260,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b535 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 134 76 26 304 96 65 129 260), lower := (rows 35 134 76 26 304 96 65 129 256), losses := [] }

theorem u535 : Upper (D 6) (R 6) [34,132,72,18,288,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b536 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 377, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 134 76 26 304 96 65 132 257), lower := (rows 35 134 76 26 304 96 65 132 256), losses := [] }

theorem u536 : Upper (D 6) (R 6) [34,132,72,18,288,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b537 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 272, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 76 56 274 96 65 129 260), lower := (rows 35 134 76 56 274 96 65 129 256), losses := [] }

theorem u537 : Upper (D 6) (R 6) [34,132,72,48,258,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b538 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 377, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 134 76 56 274 96 65 132 257), lower := (rows 35 134 76 56 274 96 65 132 256), losses := [] }

theorem u538 : Upper (D 6) (R 6) [34,132,72,48,258,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b539 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 134 100 25 276 40 66 129 320), lower := (rows 35 134 100 25 276 40 66 129 256), losses := [] }

theorem u539 : Upper (D 6) (R 6) [34,132,96,17,260,8,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b539 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u539
end Delivery.IrregularNine14.P06
