import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0007
import IrregularNine14P06C0008

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6480 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 88 280 36 68 161 289), lower := (rows 35 131 70 88 280 36 68 128 256), losses := [] }

theorem u6480 : Upper (D 6) (R 6) [34,129,66,80,264,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6481 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 68, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 70 88 280 36 96 133 261), lower := (rows 35 131 70 88 280 36 96 128 256), losses := [] }

theorem u6481 : Upper (D 6) (R 6) [34,129,66,80,264,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6482 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 70 88 304 36 65 140 268), lower := (rows 35 131 70 88 304 36 65 128 256), losses := [] }

theorem u6482 : Upper (D 6) (R 6) [34,129,66,80,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6483 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,5)], upper := (rows 35 131 70 88 304 36 68 137 265), lower := (rows 35 131 70 88 304 36 68 128 256), losses := [] }

theorem u6483 : Upper (D 6) (R 6) [34,129,66,80,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6484 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 88 304 36 72 133 261), lower := (rows 35 131 70 88 304 36 72 128 256), losses := [] }

theorem u6484 : Upper (D 6) (R 6) [34,129,66,80,288,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6484 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6485 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 104 276 48 65 140 268), lower := (rows 35 131 70 104 276 48 65 128 256), losses := [] }

theorem u6485 : Upper (D 6) (R 6) [34,129,66,96,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6485 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6486 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 70 104 276 48 68 137 265), lower := (rows 35 131 70 104 276 48 68 128 256), losses := [] }

theorem u6486 : Upper (D 6) (R 6) [34,129,66,96,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6486 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6487 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 131 70 104 276 48 72 133 261), lower := (rows 35 131 70 104 276 48 72 128 256), losses := [] }

theorem u6487 : Upper (D 6) (R 6) [34,129,66,96,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6487 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6488 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 387, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 13 22 96 80 416 288), lower := (rows 35 131 76 13 22 96 80 128 256), losses := [] }

theorem u6488 : Upper (D 6) (R 6) [34,129,72,5,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6488 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6489 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 131 76 13 22 96 96 400 272), lower := (rows 35 131 76 13 22 96 96 128 256), losses := [] }

theorem u6489 : Upper (D 6) (R 6) [34,129,72,5,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6490 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 483, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 76 13 22 96 320 176 304), lower := (rows 35 131 76 13 22 96 320 128 256), losses := [] }

theorem u6490 : Upper (D 6) (R 6) [34,129,72,5,6,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6490 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6491 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 289, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 13 82 288 68 176 304), lower := (rows 35 131 76 13 82 288 68 128 256), losses := [] }

theorem u6491 : Upper (D 6) (R 6) [34,129,72,5,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6491 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6492 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 92, targets := 32 }], pairs := [(2,5)], upper := (rows 35 131 76 13 82 288 80 164 292), lower := (rows 35 131 76 13 82 288 80 128 256), losses := [] }

theorem u6492 : Upper (D 6) (R 6) [34,129,72,5,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6492 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6493 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 13 82 288 96 148 276), lower := (rows 35 131 76 13 82 288 96 128 256), losses := [] }

theorem u6493 : Upper (D 6) (R 6) [34,129,72,5,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6493 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6494 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 131 76 13 112 288 66 148 276), lower := (rows 35 131 76 13 112 288 66 128 256), losses := [] }

theorem u6494 : Upper (D 6) (R 6) [34,129,72,5,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6494 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6495 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 13 112 288 68 146 274), lower := (rows 35 131 76 13 112 288 68 128 256), losses := [] }

theorem u6495 : Upper (D 6) (R 6) [34,129,72,5,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6495 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6496 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1)], upper := (rows 35 131 76 13 112 288 80 134 262), lower := (rows 35 131 76 13 112 288 80 128 256), losses := [] }

theorem u6496 : Upper (D 6) (R 6) [34,129,72,5,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6496 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6497 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 403, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 13 274 96 68 176 304), lower := (rows 35 131 76 13 274 96 68 128 256), losses := [] }

theorem u6497 : Upper (D 6) (R 6) [34,129,72,5,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6498 : Route 9 := (fun mask => (mask,id))

def c6498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6498 : Upper (D 6) (R 6) [34,129,72,5,258,64,16] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,258,64,16] 13 (by decide) (choices 1) [4,32] r6498 c6498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u479
  · exact u480

def b6499 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 131 76 13 274 96 96 148 276), lower := (rows 35 131 76 13 274 96 96 128 256), losses := [] }

theorem u6499 : Upper (D 6) (R 6) [34,129,72,5,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6500 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 32 },{ cop := 2, region := 304, targets := 1 }], pairs := [(2,5),(3,5),(4,0)], upper := (rows 35 131 76 13 276 96 66 176 304), lower := (rows 35 131 76 13 276 96 66 128 256), losses := [] }

theorem u6500 : Upper (D 6) (R 6) [34,129,72,5,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6501 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 13 276 96 80 162 290), lower := (rows 35 131 76 13 276 96 80 128 256), losses := [] }

theorem u6501 : Upper (D 6) (R 6) [34,129,72,5,260,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6501 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6502 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 131 76 13 276 96 96 146 274), lower := (rows 35 131 76 13 276 96 96 128 256), losses := [] }

theorem u6502 : Upper (D 6) (R 6) [34,129,72,5,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6503 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 32 },{ cop := 2, region := 304, targets := 1 }], pairs := [(2,5),(3,5),(4,0)], upper := (rows 35 131 76 13 304 96 66 148 276), lower := (rows 35 131 76 13 304 96 66 128 256), losses := [] }

theorem u6503 : Upper (D 6) (R 6) [34,129,72,5,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6504 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 403, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 13 304 96 68 146 274), lower := (rows 35 131 76 13 304 96 68 128 256), losses := [] }

theorem u6504 : Upper (D 6) (R 6) [34,129,72,5,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6505 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 76 13 304 96 80 134 262), lower := (rows 35 131 76 13 304 96 80 128 256), losses := [] }

theorem u6505 : Upper (D 6) (R 6) [34,129,72,5,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6505 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6506 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 76, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 131 76 13 336 48 66 164 292), lower := (rows 35 131 76 13 336 48 66 128 256), losses := [] }

theorem u6506 : Upper (D 6) (R 6) [34,129,72,5,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6506 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6507 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 76, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 35 131 76 13 336 48 68 162 290), lower := (rows 35 131 76 13 336 48 68 128 256), losses := [] }

theorem u6507 : Upper (D 6) (R 6) [34,129,72,5,320,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6507 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6508 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 76 13 336 48 96 134 262), lower := (rows 35 131 76 13 336 48 96 128 256), losses := [] }

theorem u6508 : Upper (D 6) (R 6) [34,129,72,5,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6508 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6509 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 387, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 14 21 96 80 416 288), lower := (rows 35 131 76 14 21 96 80 128 256), losses := [] }

theorem u6509 : Upper (D 6) (R 6) [34,129,72,6,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6509 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6510 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 131 76 14 21 96 96 400 272), lower := (rows 35 131 76 14 21 96 96 128 256), losses := [] }

theorem u6510 : Upper (D 6) (R 6) [34,129,72,6,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6511 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 483, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 76 14 21 96 320 176 304), lower := (rows 35 131 76 14 21 96 320 128 256), losses := [] }

theorem u6511 : Upper (D 6) (R 6) [34,129,72,6,5,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6511 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6512 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 419, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 14 81 288 68 176 304), lower := (rows 35 131 76 14 81 288 68 128 256), losses := [] }

theorem u6512 : Upper (D 6) (R 6) [34,129,72,6,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6512 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6513 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 92, targets := 32 }], pairs := [(2,5)], upper := (rows 35 131 76 14 81 288 80 164 292), lower := (rows 35 131 76 14 81 288 80 128 256), losses := [] }

theorem u6513 : Upper (D 6) (R 6) [34,129,72,6,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6513 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6514 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 142, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 14 81 288 96 148 276), lower := (rows 35 131 76 14 81 288 96 128 256), losses := [] }

theorem u6514 : Upper (D 6) (R 6) [34,129,72,6,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6514 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6515 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 131 76 14 112 288 65 148 276), lower := (rows 35 131 76 14 112 288 65 128 256), losses := [] }

theorem u6515 : Upper (D 6) (R 6) [34,129,72,6,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6515 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6516 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 76, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 35 131 76 14 112 288 68 145 273), lower := (rows 35 131 76 14 112 288 68 128 256), losses := [] }

theorem u6516 : Upper (D 6) (R 6) [34,129,72,6,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6516 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6517 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0)], upper := (rows 35 131 76 14 112 288 80 133 261), lower := (rows 35 131 76 14 112 288 80 128 256), losses := [] }

theorem u6517 : Upper (D 6) (R 6) [34,129,72,6,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6517 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6518 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 403, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 14 273 96 68 176 304), lower := (rows 35 131 76 14 273 96 68 128 256), losses := [] }

theorem u6518 : Upper (D 6) (R 6) [34,129,72,6,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6519 : Route 9 := (fun mask => (mask,id))

def c6519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6519 : Upper (D 6) (R 6) [34,129,72,6,257,64,16] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,257,64,16] 13 (by decide) (choices 1) [4,32] r6519 c6519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u481
  · exact u482

def b6520 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 1 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(3,0)], upper := (rows 35 131 76 14 273 96 96 148 276), lower := (rows 35 131 76 14 273 96 96 128 256), losses := [] }

theorem u6520 : Upper (D 6) (R 6) [34,129,72,6,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6521 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 32 },{ cop := 2, region := 304, targets := 1 }], pairs := [(2,5),(3,5),(4,0)], upper := (rows 35 131 76 14 276 96 65 176 304), lower := (rows 35 131 76 14 276 96 65 128 256), losses := [] }

theorem u6521 : Upper (D 6) (R 6) [34,129,72,6,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6522 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 14 276 96 80 161 289), lower := (rows 35 131 76 14 276 96 80 128 256), losses := [] }

theorem u6522 : Upper (D 6) (R 6) [34,129,72,6,260,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6522 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6523 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 1 },{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(3,0)], upper := (rows 35 131 76 14 276 96 96 145 273), lower := (rows 35 131 76 14 276 96 96 128 256), losses := [] }

theorem u6523 : Upper (D 6) (R 6) [34,129,72,6,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6524 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 32 },{ cop := 2, region := 304, targets := 1 }], pairs := [(2,5),(3,5),(4,0)], upper := (rows 35 131 76 14 304 96 65 148 276), lower := (rows 35 131 76 14 304 96 65 128 256), losses := [] }

theorem u6524 : Upper (D 6) (R 6) [34,129,72,6,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6525 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 403, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 14 304 96 68 145 273), lower := (rows 35 131 76 14 304 96 68 128 256), losses := [] }

theorem u6525 : Upper (D 6) (R 6) [34,129,72,6,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6526 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 76 14 304 96 80 133 261), lower := (rows 35 131 76 14 304 96 80 128 256), losses := [] }

theorem u6526 : Upper (D 6) (R 6) [34,129,72,6,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6526 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6527 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 76, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 131 76 14 336 48 65 164 292), lower := (rows 35 131 76 14 336 48 65 128 256), losses := [] }

theorem u6527 : Upper (D 6) (R 6) [34,129,72,6,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6527 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6528 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 76, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 35 131 76 14 336 48 68 161 289), lower := (rows 35 131 76 14 336 48 68 128 256), losses := [] }

theorem u6528 : Upper (D 6) (R 6) [34,129,72,6,320,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6528 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6529 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 76 14 336 48 96 133 261), lower := (rows 35 131 76 14 336 48 96 128 256), losses := [] }

theorem u6529 : Upper (D 6) (R 6) [34,129,72,6,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6529 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6530 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 3, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 25 274 96 68 164 292), lower := (rows 35 131 76 25 274 96 68 128 256), losses := [] }

theorem u6530 : Upper (D 6) (R 6) [34,129,72,17,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6531 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 76 25 274 96 96 132 260), lower := (rows 35 131 76 25 274 96 96 128 256), losses := [] }

theorem u6531 : Upper (D 6) (R 6) [34,129,72,17,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6532 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 76 25 276 96 66 164 292), lower := (rows 35 131 76 25 276 96 66 128 256), losses := [] }

theorem u6532 : Upper (D 6) (R 6) [34,129,72,17,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6533 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 25 276 96 68 162 290), lower := (rows 35 131 76 25 276 96 68 128 256), losses := [] }

theorem u6533 : Upper (D 6) (R 6) [34,129,72,17,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6534 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 76 25 276 96 96 134 262), lower := (rows 35 131 76 25 276 96 96 128 256), losses := [] }

theorem u6534 : Upper (D 6) (R 6) [34,129,72,17,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6535 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 131 76 25 304 36 66 196 324), lower := (rows 35 131 76 25 304 36 66 128 256), losses := [] }

theorem u6535 : Upper (D 6) (R 6) [34,129,72,17,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6536 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,0),(2,1)], upper := (rows 35 131 76 25 304 36 68 194 322), lower := (rows 35 131 76 25 304 36 68 128 256), losses := [] }

theorem u6536 : Upper (D 6) (R 6) [34,129,72,17,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6537 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 131 76 25 304 96 66 132 260), lower := (rows 35 131 76 25 304 96 66 128 256), losses := [] }

theorem u6537 : Upper (D 6) (R 6) [34,129,72,17,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6538 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,0),(2,1)], upper := (rows 35 131 76 25 304 96 68 134 262), lower := (rows 35 131 76 25 304 96 68 128 256), losses := [] }

theorem u6538 : Upper (D 6) (R 6) [34,129,72,17,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6539 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 304, targets := 3 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 76 25 336 36 66 164 292), lower := (rows 35 131 76 25 336 36 66 128 256), losses := [] }

theorem u6539 : Upper (D 6) (R 6) [34,129,72,17,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6539
end Delivery.IrregularNine14.P06
