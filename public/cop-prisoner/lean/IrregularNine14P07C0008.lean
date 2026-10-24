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

def b480 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 326, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 322 14 152 112 33 192 129 260), lower := (rows 35 322 14 152 112 33 192 129 256), losses := [] }

theorem u480 : Upper (D 7) (R 7) [34,320,10,144,96,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b481 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 220, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 322 14 152 112 33 192 132 257), lower := (rows 35 322 14 152 112 33 192 132 256), losses := [] }

theorem u481 : Upper (D 7) (R 7) [34,320,10,144,96,1,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b481 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b482 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 80, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 322 14 152 112 160 65 129 260), lower := (rows 35 322 14 152 112 160 65 129 256), losses := [] }

theorem u482 : Upper (D 7) (R 7) [34,320,10,144,96,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b483 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 188, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 322 14 152 112 160 65 132 257), lower := (rows 35 322 14 152 112 160 65 132 256), losses := [] }

theorem u483 : Upper (D 7) (R 7) [34,320,10,144,96,128,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b483 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b484 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 14 168 81 33 192 132 272), lower := (rows 35 322 14 168 81 33 192 132 256), losses := [] }

theorem u484 : Upper (D 7) (R 7) [34,320,10,160,65,1,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b484 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b485 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 326, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 322 14 168 81 33 192 144 260), lower := (rows 35 322 14 168 81 33 192 144 256), losses := [] }

theorem u485 : Upper (D 7) (R 7) [34,320,10,160,65,1,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b485 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b486 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 72, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,6),(3,1),(4,5),(4,6)], upper := (rows 35 322 28 104 146 160 65 129 260), lower := (rows 35 322 28 104 146 160 65 129 256), losses := [] }

theorem u486 : Upper (D 7) (R 7) [34,320,24,96,130,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b487 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 188, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 322 28 104 146 160 65 132 257), lower := (rows 35 322 28 104 146 160 65 132 256), losses := [] }

theorem u487 : Upper (D 7) (R 7) [34,320,24,96,130,128,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b487 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b488 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 270, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 322 28 138 208 33 96 129 260), lower := (rows 35 322 28 138 208 33 96 129 256), losses := [] }

theorem u488 : Upper (D 7) (R 7) [34,320,24,130,192,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b489 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 156, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 35 322 28 138 208 33 96 132 257), lower := (rows 35 322 28 138 208 33 96 132 256), losses := [] }

theorem u489 : Upper (D 7) (R 7) [34,320,24,130,192,1,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b489 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b490 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 322 76 138 145 48 96 129 260), lower := (rows 35 322 76 138 145 48 96 129 256), losses := [] }

theorem u490 : Upper (D 7) (R 7) [34,320,72,130,129,16,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b490 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b491 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 140, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 35 322 76 138 145 48 96 132 257), lower := (rows 35 322 76 138 145 48 96 132 256), losses := [] }

theorem u491 : Upper (D 7) (R 7) [34,320,72,130,129,16,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b491 [(5,4),(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b492 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 346, targets := 1 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 37 42 69 328 146 160 66 129 272), lower := (rows 37 42 69 328 146 160 66 129 256), losses := [] }

theorem u492 : Upper (D 7) (R 7) [36,40,65,320,130,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b493 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 42 69 328 146 160 66 144 257), lower := (rows 37 42 69 328 146 160 66 144 256), losses := [] }

theorem u493 : Upper (D 7) (R 7) [36,40,65,320,130,128,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b493 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b494 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 264, targets := 161 }], pairs := [(3,0),(3,5),(3,7)], upper := (rows 37 42 70 328 145 48 192 129 258), lower := (rows 37 42 70 328 145 48 192 129 256), losses := [] }

theorem u494 : Upper (D 7) (R 7) [36,40,66,320,129,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b494 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b495 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 196, targets := 33 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(2,0),(2,5)], upper := (rows 37 42 70 328 145 48 192 130 257), lower := (rows 37 42 70 328 145 48 192 130 256), losses := [] }

theorem u495 : Upper (D 7) (R 7) [36,40,66,320,129,16,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b495 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b496 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 264, targets := 161 }], pairs := [(3,0),(3,5),(3,7)], upper := (rows 37 42 70 328 145 160 80 129 258), lower := (rows 37 42 70 328 145 160 80 129 256), losses := [] }

theorem u496 : Upper (D 7) (R 7) [36,40,66,320,129,128,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b496 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b497 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 3, region := 162, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 37 42 70 328 145 160 80 130 257), lower := (rows 37 42 70 328 145 160 80 130 256), losses := [] }

theorem u497 : Upper (D 7) (R 7) [36,40,66,320,129,128,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b497 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b498 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 144, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 37 42 84 200 145 288 66 129 258), lower := (rows 37 42 84 200 145 288 66 129 256), losses := [] }

theorem u498 : Upper (D 7) (R 7) [36,40,80,192,129,256,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b498 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b499 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 289, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 42 84 200 145 288 66 130 257), lower := (rows 37 42 84 200 145 288 66 130 256), losses := [] }

theorem u499 : Upper (D 7) (R 7) [36,40,80,192,129,256,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b499 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b500 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 310, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 42 84 200 146 288 65 129 258), lower := (rows 37 42 84 200 146 288 65 129 256), losses := [] }

theorem u500 : Upper (D 7) (R 7) [36,40,80,192,130,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b500 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b501 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 144, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 37 42 84 200 146 288 65 130 257), lower := (rows 37 42 84 200 146 288 65 130 256), losses := [] }

theorem u501 : Upper (D 7) (R 7) [36,40,80,192,130,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b501 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b502 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(3,1)], upper := (rows 37 42 84 200 400 33 66 129 258), lower := (rows 37 42 84 200 400 33 66 129 256), losses := [] }

theorem u502 : Upper (D 7) (R 7) [36,40,80,192,384,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b503 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 202, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 42 84 200 400 33 66 130 257), lower := (rows 37 42 84 200 400 33 66 130 256), losses := [] }

theorem u503 : Upper (D 7) (R 7) [36,40,80,192,384,1,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b504 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 310, targets := 1 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 37 42 84 200 400 34 65 129 258), lower := (rows 37 42 84 200 400 34 65 129 256), losses := [] }

theorem u504 : Upper (D 7) (R 7) [36,40,80,192,384,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b505 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 170, targets := 1 },{ cop := 3, region := 34, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 42 84 200 400 34 65 130 257), lower := (rows 37 42 84 200 400 34 65 130 256), losses := [] }

theorem u505 : Upper (D 7) (R 7) [36,40,80,192,384,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b506 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 37 42 196 328 146 34 65 129 272), lower := (rows 37 42 196 328 146 34 65 129 256), losses := [] }

theorem u506 : Upper (D 7) (R 7) [36,40,192,320,130,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b507 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 42 196 328 146 34 65 144 257), lower := (rows 37 42 196 328 146 34 65 144 256), losses := [] }

theorem u507 : Upper (D 7) (R 7) [36,40,192,320,130,2,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b507 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b508 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 266, targets := 160 }], pairs := [(1,5),(1,7),(3,5),(3,7)], upper := (rows 37 74 7 266 208 160 96 129 272), lower := (rows 37 74 7 266 208 160 96 129 256), losses := [] }

theorem u508 : Upper (D 7) (R 7) [36,72,3,258,192,128,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b509 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 266 208 160 96 144 257), lower := (rows 37 74 7 266 208 160 96 144 256), losses := [] }

theorem u509 : Upper (D 7) (R 7) [36,72,3,258,192,128,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b509 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b510 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 161 },{ cop := 8, region := 245, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 37 74 21 138 336 160 96 129 258), lower := (rows 37 74 21 138 336 160 96 129 256), losses := [] }

theorem u510 : Upper (D 7) (R 7) [36,72,17,130,320,128,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b511 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 341, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 21 138 336 160 96 130 257), lower := (rows 37 74 21 138 336 160 96 130 256), losses := [] }

theorem u511 : Upper (D 7) (R 7) [36,72,17,130,320,128,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b512 : PairBound 9 := { available := 2, camps := [{ cop := 7, region := 378, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 21 168 208 34 320 129 258), lower := (rows 37 74 21 168 208 34 320 129 256), losses := [] }

theorem u512 : Upper (D 7) (R 7) [36,72,17,160,192,2,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b512 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b513 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 74 21 168 208 34 320 130 257), lower := (rows 37 74 21 168 208 34 320 130 256), losses := [] }

theorem u513 : Upper (D 7) (R 7) [36,72,17,160,192,2,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b513 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b514 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 7, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 74 21 392 208 34 96 129 258), lower := (rows 37 74 21 392 208 34 96 129 256), losses := [] }

theorem u514 : Upper (D 7) (R 7) [36,72,17,384,192,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b515 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 37 74 21 392 208 34 96 130 257), lower := (rows 37 74 21 392 208 34 96 130 256), losses := [] }

theorem u515 : Upper (D 7) (R 7) [36,72,17,384,192,2,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b516 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 37 74 22 168 145 96 320 129 258), lower := (rows 37 74 22 168 145 96 320 129 256), losses := [] }

theorem u516 : Upper (D 7) (R 7) [36,72,18,160,129,64,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b516 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b517 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 353, targets := 130 },{ cop := 5, region := 138, targets := 1 }], pairs := [(0,1),(0,7),(1,0)], upper := (rows 37 74 22 168 145 96 320 130 257), lower := (rows 37 74 22 168 145 96 320 130 256), losses := [] }

theorem u517 : Upper (D 7) (R 7) [36,72,18,160,129,64,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b517 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b518 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 233, targets := 2 },{ cop := 0, region := 136, targets := 64 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(3,6)], upper := (rows 37 74 22 168 400 96 65 129 258), lower := (rows 37 74 22 168 400 96 65 129 256), losses := [] }

theorem u518 : Upper (D 7) (R 7) [36,72,18,160,384,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b519 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 5, region := 138, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 37 74 22 168 400 96 65 130 257), lower := (rows 37 74 22 168 400 96 65 130 256), losses := [] }

theorem u519 : Upper (D 7) (R 7) [36,72,18,160,384,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b520 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 266, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 22 296 145 96 192 129 258), lower := (rows 37 74 22 296 145 96 192 129 256), losses := [] }

theorem u520 : Upper (D 7) (R 7) [36,72,18,288,129,64,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b521 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 264, targets := 194 },{ cop := 8, region := 234, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 37 74 22 296 145 96 192 130 257), lower := (rows 37 74 22 296 145 96 192 130 256), losses := [] }

theorem u521 : Upper (D 7) (R 7) [36,72,18,288,129,64,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b522 : PairBound 9 := { available := 16, camps := [{ cop := 6, region := 314, targets := 1 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 37 74 69 296 146 34 192 129 272), lower := (rows 37 74 69 296 146 34 192 129 256), losses := [] }

theorem u522 : Upper (D 7) (R 7) [36,72,65,288,130,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b523 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 69 296 146 34 192 144 257), lower := (rows 37 74 69 296 146 34 192 144 256), losses := [] }

theorem u523 : Upper (D 7) (R 7) [36,72,65,288,130,2,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b523 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b524 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 374, targets := 1 },{ cop := 7, region := 8, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 37 74 84 137 400 34 96 129 258), lower := (rows 37 74 84 137 400 34 96 129 256), losses := [] }

theorem u524 : Upper (D 7) (R 7) [36,72,80,129,384,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b525 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 272, targets := 98 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,6)], upper := (rows 37 74 84 137 400 34 96 130 257), lower := (rows 37 74 84 137 400 34 96 130 256), losses := [] }

theorem u525 : Upper (D 7) (R 7) [36,72,80,129,384,2,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b526 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 296, targets := 65 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(3,0),(3,6)], upper := (rows 37 74 84 168 146 288 65 129 258), lower := (rows 37 74 84 168 146 288 65 129 256), losses := [] }

theorem u526 : Upper (D 7) (R 7) [36,72,80,160,130,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b526 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b527 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 148, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 74 84 168 146 288 65 130 257), lower := (rows 37 74 84 168 146 288 65 130 256), losses := [] }

theorem u527 : Upper (D 7) (R 7) [36,72,80,160,130,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b527 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b528 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 136, targets := 2 },{ cop := 0, region := 136, targets := 64 }], pairs := [(2,0),(3,1),(3,6),(4,0)], upper := (rows 37 74 84 168 400 34 65 129 258), lower := (rows 37 74 84 168 400 34 65 129 256), losses := [{ target := 0, region := (rows 0 2 6 8 24 34 64 128 290), good := (rows 292 382 84 440 400 294 64 128 256) }] }

theorem u528 : Upper (D 7) (R 7) [36,72,80,160,384,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b529 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 341, targets := 2 },{ cop := 1, region := 168, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 37 74 84 168 400 34 65 130 257), lower := (rows 37 74 84 168 400 34 65 130 256), losses := [] }

theorem u529 : Upper (D 7) (R 7) [36,72,80,160,384,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b530 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 152 304 96 66 129 258), lower := (rows 37 74 133 152 304 96 66 129 256), losses := [] }

theorem u530 : Upper (D 7) (R 7) [36,72,129,144,288,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b531 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 194 },{ cop := 8, region := 250, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 37 74 133 152 304 96 66 130 257), lower := (rows 37 74 133 152 304 96 66 130 256), losses := [] }

theorem u531 : Upper (D 7) (R 7) [36,72,129,144,288,64,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b532 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 133 296 146 96 80 129 258), lower := (rows 37 74 133 296 146 96 80 129 256), losses := [] }

theorem u532 : Upper (D 7) (R 7) [36,72,129,288,130,64,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b532 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b533 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 264, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 37 74 133 296 146 96 80 130 257), lower := (rows 37 74 133 296 146 96 80 130 256), losses := [] }

theorem u533 : Upper (D 7) (R 7) [36,72,129,288,130,64,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b533 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b534 : PairBound 9 := { available := 64, camps := [{ cop := 7, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 133 392 19 34 80 160 320), lower := (rows 37 74 133 392 19 34 80 160 256), losses := [] }

theorem u534 : Upper (D 7) (R 7) [36,72,129,384,3,2,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b534 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b535 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 37 74 133 392 19 34 80 192 288), lower := (rows 37 74 133 392 19 34 80 192 256), losses := [] }

theorem u535 : Upper (D 7) (R 7) [36,72,129,384,3,2,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b535 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b536 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 132, targets := 32 }], pairs := [(1,0),(2,5),(3,0)], upper := (rows 37 74 133 392 19 96 80 130 288), lower := (rows 37 74 133 392 19 96 80 130 256), losses := [] }

theorem u536 : Upper (D 7) (R 7) [36,72,129,384,3,64,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b536 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b537 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 133 392 19 96 80 160 258), lower := (rows 37 74 133 392 19 96 80 160 256), losses := [] }

theorem u537 : Upper (D 7) (R 7) [36,72,129,384,3,64,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b537 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b538 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 304, targets := 129 },{ cop := 2, region := 97, targets := 2 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(4,0),(4,7)], upper := (rows 37 74 134 152 274 96 65 129 288), lower := (rows 37 74 134 152 274 96 65 129 256), losses := [] }

theorem u538 : Upper (D 7) (R 7) [36,72,130,144,258,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b539 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 1, region := 164, targets := 1 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(0,7),(2,0),(4,7)], upper := (rows 37 74 134 152 274 96 65 160 257), lower := (rows 37 74 134 152 274 96 65 160 256), losses := [] }

theorem u539 : Upper (D 7) (R 7) [36,72,130,144,258,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u539
end Delivery.IrregularNine14.P07
