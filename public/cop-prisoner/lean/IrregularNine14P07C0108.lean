import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0007
import IrregularNine14P07C0008

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6480 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 322 14 73 145 160 68 176 304), lower := (rows 35 322 14 73 145 160 68 128 256), losses := [] }

theorem u6480 : Upper (D 7) (R 7) [34,320,10,65,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6480 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6481 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 3, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 322 14 73 145 160 80 164 292), lower := (rows 35 322 14 73 145 160 80 128 256), losses := [] }

theorem u6481 : Upper (D 7) (R 7) [34,320,10,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6481 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6482 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 76, targets := 128 }], pairs := [(1,5),(2,5),(2,7),(4,5)], upper := (rows 35 322 14 73 145 160 96 148 276), lower := (rows 35 322 14 73 145 160 96 128 256), losses := [] }

theorem u6482 : Upper (D 7) (R 7) [34,320,10,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6483 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 322 14 73 148 160 65 176 304), lower := (rows 35 322 14 73 148 160 65 128 256), losses := [] }

theorem u6483 : Upper (D 7) (R 7) [34,320,10,65,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6484 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 322 14 73 148 160 80 161 289), lower := (rows 35 322 14 73 148 160 80 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 189 84 137 265), good := (rows 417 320 508 489 244 160 112 160 256) }] }

theorem u6484 : Upper (D 7) (R 7) [34,320,10,65,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6484 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6485 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 76, targets := 128 }], pairs := [(1,5),(2,5),(2,7),(4,5)], upper := (rows 35 322 14 73 148 160 96 145 273), lower := (rows 35 322 14 73 148 160 96 128 256), losses := [] }

theorem u6485 : Upper (D 7) (R 7) [34,320,10,65,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6486 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 322 14 88 52 160 65 129 385), lower := (rows 35 322 14 88 52 160 65 128 256), losses := [] }

theorem u6486 : Upper (D 7) (R 7) [34,320,10,80,36,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6487 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(2,0),(4,6)], upper := (rows 35 322 14 88 52 160 192 129 257), lower := (rows 35 322 14 88 52 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 7 27 19 224 224 128 256), good := (rows 126 382 30 120 124 224 224 224 256) }] }

theorem u6487 : Upper (D 7) (R 7) [34,320,10,80,36,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6488 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 322 14 88 145 33 68 160 416), lower := (rows 35 322 14 88 145 33 68 128 256), losses := [] }

theorem u6488 : Upper (D 7) (R 7) [34,320,10,80,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6488 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6489 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 322 14 88 145 33 96 132 388), lower := (rows 35 322 14 88 145 33 96 128 256), losses := [] }

theorem u6489 : Upper (D 7) (R 7) [34,320,10,80,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6490 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 35 322 14 88 145 33 192 164 292), lower := (rows 35 322 14 88 145 33 192 128 256), losses := [] }

theorem u6490 : Upper (D 7) (R 7) [34,320,10,80,129,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6491 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 3, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(2,0),(4,6)], upper := (rows 35 322 14 88 145 160 65 164 292), lower := (rows 35 322 14 88 145 160 65 128 256), losses := [] }

theorem u6491 : Upper (D 7) (R 7) [34,320,10,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6492 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 322 14 88 145 160 68 161 289), lower := (rows 35 322 14 88 145 160 68 128 256), losses := [] }

theorem u6492 : Upper (D 7) (R 7) [34,320,10,80,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6492 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6493 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 104, targets := 3 }], pairs := [(0,6),(3,0),(3,1),(4,6)], upper := (rows 35 322 14 88 145 160 96 133 261), lower := (rows 35 322 14 88 145 160 96 128 256), losses := [] }

theorem u6493 : Upper (D 7) (R 7) [34,320,10,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6494 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 14 88 148 33 65 160 416), lower := (rows 35 322 14 88 148 33 65 128 256), losses := [] }

theorem u6494 : Upper (D 7) (R 7) [34,320,10,80,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6495 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 14 88 148 33 96 129 385), lower := (rows 35 322 14 88 148 33 96 128 256), losses := [] }

theorem u6495 : Upper (D 7) (R 7) [34,320,10,80,132,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6496 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 322 14 88 148 33 192 161 289), lower := (rows 35 322 14 88 148 33 192 128 256), losses := [] }

theorem u6496 : Upper (D 7) (R 7) [34,320,10,80,132,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6497 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 322 14 88 176 33 65 132 388), lower := (rows 35 322 14 88 176 33 65 128 256), losses := [] }

theorem u6497 : Upper (D 7) (R 7) [34,320,10,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6498 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 322 14 88 176 33 68 129 385), lower := (rows 35 322 14 88 176 33 68 128 256), losses := [] }

theorem u6498 : Upper (D 7) (R 7) [34,320,10,80,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6498 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6499 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 322 14 88 176 33 192 133 261), lower := (rows 35 322 14 88 176 33 192 128 256), losses := [] }

theorem u6499 : Upper (D 7) (R 7) [34,320,10,80,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6500 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 322 14 104 145 48 65 132 388), lower := (rows 35 322 14 104 145 48 65 128 256), losses := [] }

theorem u6500 : Upper (D 7) (R 7) [34,320,10,96,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6500 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6501 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 322 14 104 145 48 68 129 385), lower := (rows 35 322 14 104 145 48 68 128 256), losses := [] }

theorem u6501 : Upper (D 7) (R 7) [34,320,10,96,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6501 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6502 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 14 104 145 48 192 133 261), lower := (rows 35 322 14 104 145 48 192 128 256), losses := [] }

theorem u6502 : Upper (D 7) (R 7) [34,320,10,96,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6502 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6503 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,6)], upper := (rows 35 322 14 104 145 160 65 148 276), lower := (rows 35 322 14 104 145 160 65 128 256), losses := [] }

theorem u6503 : Upper (D 7) (R 7) [34,320,10,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6504 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 1 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 35 322 14 104 145 160 68 145 273), lower := (rows 35 322 14 104 145 160 68 128 256), losses := [] }

theorem u6504 : Upper (D 7) (R 7) [34,320,10,96,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6504 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6505 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 14 104 145 160 80 133 261), lower := (rows 35 322 14 104 145 160 80 128 256), losses := [] }

theorem u6505 : Upper (D 7) (R 7) [34,320,10,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6505 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6506 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,6)], upper := (rows 35 322 14 104 148 160 65 145 273), lower := (rows 35 322 14 104 148 160 65 128 256), losses := [] }

theorem u6506 : Upper (D 7) (R 7) [34,320,10,96,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6507 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 14 104 148 160 80 129 257), lower := (rows 35 322 14 104 148 160 80 128 256), losses := [] }

theorem u6507 : Upper (D 7) (R 7) [34,320,10,96,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6507 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6508 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 168, targets := 66 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 35 322 14 137 81 160 68 176 304), lower := (rows 35 322 14 137 81 160 68 128 256), losses := [] }

theorem u6508 : Upper (D 7) (R 7) [34,320,10,129,65,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6508 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6509 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 35 322 14 137 81 160 80 164 292), lower := (rows 35 322 14 137 81 160 80 128 256), losses := [] }

theorem u6509 : Upper (D 7) (R 7) [34,320,10,129,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6509 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6510 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 322 14 137 81 160 96 148 276), lower := (rows 35 322 14 137 81 160 96 128 256), losses := [] }

theorem u6510 : Upper (D 7) (R 7) [34,320,10,129,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6511 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 418, targets := 1 }], pairs := [(0,6),(1,0),(4,1),(4,5)], upper := (rows 35 322 14 137 84 160 65 176 304), lower := (rows 35 322 14 137 84 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 188 73 148 276), good := (rows 97 320 508 233 500 160 65 160 256) },{ target := 5, region := (rows 1 2 4 8 20 0 73 128 256), good := (rows 67 322 94 201 84 128 65 128 256) },{ target := 6, region := (rows 5 2 4 24 16 184 0 144 272), good := (rows 35 258 47 169 445 160 1 160 256) }] }

theorem u6511 : Upper (D 7) (R 7) [34,320,10,129,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6512 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 322 14 137 84 160 80 161 289), lower := (rows 35 322 14 137 84 160 80 128 256), losses := [] }

theorem u6512 : Upper (D 7) (R 7) [34,320,10,129,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6512 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6513 : PairBound 9 := { available := 17, camps := [], pairs := [(0,6),(3,6),(4,0),(4,1)], upper := (rows 35 322 14 137 84 160 96 145 273), lower := (rows 35 322 14 137 84 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 237 128 256), good := (rows 98 322 126 232 84 224 96 224 256) },{ target := 1, region := (rows 1 0 4 8 20 168 237 128 256), good := (rows 97 320 124 233 84 224 96 224 256) },{ target := 6, region := (rows 5 2 4 24 16 184 0 144 272), good := (rows 35 258 47 169 445 160 32 160 256) }] }

theorem u6513 : Upper (D 7) (R 7) [34,320,10,129,68,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6514 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 130 }], pairs := [(0,6),(1,7),(4,1),(4,7)], upper := (rows 35 322 14 137 112 160 65 148 276), lower := (rows 35 322 14 137 112 160 65 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 35 258 47 169 48 160 1 160 256) },{ target := 7, region := (rows 1 14 12 8 17 32 73 0 264), good := (rows 115 322 334 351 112 32 81 0 256) }] }

theorem u6514 : Upper (D 7) (R 7) [34,320,10,129,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6515 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 259, targets := 128 }], pairs := [(0,7),(1,7),(4,0)], upper := (rows 35 322 14 137 112 160 68 145 273), lower := (rows 35 322 14 137 112 160 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 68 128 256), good := (rows 34 322 126 168 112 160 84 160 256) }] }

theorem u6515 : Upper (D 7) (R 7) [34,320,10,129,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6515 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6516 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 14 137 112 160 80 133 261), lower := (rows 35 322 14 137 112 160 80 128 256), losses := [] }

theorem u6516 : Upper (D 7) (R 7) [34,320,10,129,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6516 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6517 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,6),(0,7),(1,7)], upper := (rows 35 322 14 137 208 33 68 176 304), lower := (rows 35 322 14 137 208 33 68 128 256), losses := [] }

theorem u6517 : Upper (D 7) (R 7) [34,320,10,129,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6517 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6518 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 14 137 208 33 80 164 292), lower := (rows 35 322 14 137 208 33 80 128 256), losses := [] }

theorem u6518 : Upper (D 7) (R 7) [34,320,10,129,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6518 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6519 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 },{ cop := 3, region := 112, targets := 2 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 322 14 137 208 33 96 148 276), lower := (rows 35 322 14 137 208 33 96 128 256), losses := [] }

theorem u6519 : Upper (D 7) (R 7) [34,320,10,129,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6520 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 3, region := 80, targets := 2 }], pairs := [(2,6),(3,6),(4,1)], upper := (rows 35 322 14 137 208 48 65 164 292), lower := (rows 35 322 14 137 208 48 65 128 256), losses := [] }

theorem u6520 : Upper (D 7) (R 7) [34,320,10,129,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6520 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6521 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 322 14 137 208 48 68 161 289), lower := (rows 35 322 14 137 208 48 68 128 256), losses := [] }

theorem u6521 : Upper (D 7) (R 7) [34,320,10,129,192,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6521 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6522 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 140, targets := 96 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 35 322 14 137 208 48 96 133 261), lower := (rows 35 322 14 137 208 48 96 128 256), losses := [] }

theorem u6522 : Upper (D 7) (R 7) [34,320,10,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6522 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6523 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 4, region := 168, targets := 2 }], pairs := [(0,7),(3,1),(4,7)], upper := (rows 35 322 14 152 81 33 68 160 416), lower := (rows 35 322 14 152 81 33 68 128 256), losses := [] }

theorem u6523 : Upper (D 7) (R 7) [34,320,10,144,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6523 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6524 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 398, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 322 14 152 81 33 96 132 388), lower := (rows 35 322 14 152 81 33 96 128 256), losses := [] }

theorem u6524 : Upper (D 7) (R 7) [34,320,10,144,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6525 : Route 9 := (fun mask => (mask,id))

def c6525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6525 : Upper (D 7) (R 7) [34,320,10,144,65,1,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,65,1,128] 13 (by decide) (choices 1) [4,32] r6525 c6525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u478
  · exact u479

def b6526 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 35 322 14 152 81 160 65 164 292), lower := (rows 35 322 14 152 81 160 65 128 256), losses := [] }

theorem u6526 : Upper (D 7) (R 7) [34,320,10,144,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6527 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 168, targets := 66 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(3,6)], upper := (rows 35 322 14 152 81 160 68 161 289), lower := (rows 35 322 14 152 81 160 68 128 256), losses := [] }

theorem u6527 : Upper (D 7) (R 7) [34,320,10,144,65,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6527 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6528 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 322 14 152 81 160 96 133 261), lower := (rows 35 322 14 152 81 160 96 128 256), losses := [] }

theorem u6528 : Upper (D 7) (R 7) [34,320,10,144,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6529 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 1, region := 33, targets := 64 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,7)], upper := (rows 35 322 14 152 84 33 65 160 416), lower := (rows 35 322 14 152 84 33 65 128 256), losses := [] }

theorem u6529 : Upper (D 7) (R 7) [34,320,10,144,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6530 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 1, region := 33, targets := 64 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,7)], upper := (rows 35 322 14 152 84 33 96 129 385), lower := (rows 35 322 14 152 84 33 96 128 256), losses := [] }

theorem u6530 : Upper (D 7) (R 7) [34,320,10,144,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6531 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 291, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,0)], upper := (rows 35 322 14 152 84 33 192 161 289), lower := (rows 35 322 14 152 84 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 32 200 128 256), good := (rows 34 322 94 216 84 32 192 192 256) }] }

theorem u6531 : Upper (D 7) (R 7) [34,320,10,144,68,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6532 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 398, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 322 14 152 112 33 65 132 388), lower := (rows 35 322 14 152 112 33 65 128 256), losses := [] }

theorem u6532 : Upper (D 7) (R 7) [34,320,10,144,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6533 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,7)], upper := (rows 35 322 14 152 112 33 68 129 385), lower := (rows 35 322 14 152 112 33 68 128 256), losses := [] }

theorem u6533 : Upper (D 7) (R 7) [34,320,10,144,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6533 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6534 : Route 9 := (fun mask => (mask,id))

def c6534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6534 : Upper (D 7) (R 7) [34,320,10,144,96,1,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,96,1,128] 13 (by decide) (choices 1) [1,4] r6534 c6534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u480
  · exact u481

def r6535 : Route 9 := (fun mask => (mask,id))

def c6535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6535 : Upper (D 7) (R 7) [34,320,10,144,96,128,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,96,128,1] 13 (by decide) (choices 1) [1,4] r6535 c6535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u482
  · exact u483

def b6536 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 259, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,7)], upper := (rows 35 322 14 152 112 160 68 129 257), lower := (rows 35 322 14 152 112 160 68 128 256), losses := [] }

theorem u6536 : Upper (D 7) (R 7) [34,320,10,144,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6536 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6537 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 4, region := 386, targets := 1 }], pairs := [(0,7),(1,0),(4,7)], upper := (rows 35 322 14 168 81 33 68 144 400), lower := (rows 35 322 14 168 81 33 68 128 256), losses := [] }

theorem u6537 : Upper (D 7) (R 7) [34,320,10,160,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6537 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6538 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 14 168 81 33 80 132 388), lower := (rows 35 322 14 168 81 33 80 128 256), losses := [] }

theorem u6538 : Upper (D 7) (R 7) [34,320,10,160,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6538 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6539 : Route 9 := (fun mask => (mask,id))

def c6539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6539 : Upper (D 7) (R 7) [34,320,10,160,65,1,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,160,65,1,128] 13 (by decide) (choices 1) [4,16] r6539 c6539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u484
  · exact u485

#print axioms u6539
end Delivery.IrregularNine14.P07
