import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010
import IrregularNine14P06C0011

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8520 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 162 324 14 81 48 65 134 262), lower := (rows 41 162 324 14 81 48 65 128 256), losses := [] }

theorem u8520 : Upper (D 6) (R 6) [40,160,320,6,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8520 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8521 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 41 162 324 14 81 48 66 133 261), lower := (rows 41 162 324 14 81 48 66 128 256), losses := [] }

theorem u8521 : Upper (D 6) (R 6) [40,160,320,6,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8521 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8522 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 41 162 324 14 81 48 68 131 259), lower := (rows 41 162 324 14 81 48 68 128 256), losses := [] }

theorem u8522 : Upper (D 6) (R 6) [40,160,320,6,65,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8522 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8523 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 162 324 25 82 36 65 134 262), lower := (rows 41 162 324 25 82 36 65 128 256), losses := [] }

theorem u8523 : Upper (D 6) (R 6) [40,160,320,17,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8524 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 162 324 25 82 36 66 133 261), lower := (rows 41 162 324 25 82 36 66 128 256), losses := [] }

theorem u8524 : Upper (D 6) (R 6) [40,160,320,17,66,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8525 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 68 },{ cop := 8, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 41 162 324 25 82 36 68 131 259), lower := (rows 41 162 324 25 82 36 68 128 256), losses := [] }

theorem u8525 : Upper (D 6) (R 6) [40,160,320,17,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8526 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 97, targets := 6 },{ cop := 5, region := 390, targets := 1 }], pairs := [(0,1),(0,2),(1,0)], upper := (rows 41 162 324 26 21 96 65 134 262), lower := (rows 41 162 324 26 21 96 65 128 256), losses := [] }

theorem u8526 : Upper (D 6) (R 6) [40,160,320,18,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8527 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 98, targets := 5 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 162 324 26 21 96 66 133 261), lower := (rows 41 162 324 26 21 96 66 128 256), losses := [] }

theorem u8527 : Upper (D 6) (R 6) [40,160,320,18,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8528 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 68 },{ cop := 8, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 41 162 324 26 21 96 68 131 259), lower := (rows 41 162 324 26 21 96 68 128 256), losses := [] }

theorem u8528 : Upper (D 6) (R 6) [40,160,320,18,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8529 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 41 162 324 26 81 36 65 134 262), lower := (rows 41 162 324 26 81 36 65 128 256), losses := [] }

theorem u8529 : Upper (D 6) (R 6) [40,160,320,18,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8530 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 162 324 26 81 36 66 133 261), lower := (rows 41 162 324 26 81 36 66 128 256), losses := [] }

theorem u8530 : Upper (D 6) (R 6) [40,160,320,18,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8531 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 68 },{ cop := 8, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 41 162 324 26 81 36 68 131 259), lower := (rows 41 162 324 26 81 36 68 128 256), losses := [] }

theorem u8531 : Upper (D 6) (R 6) [40,160,320,18,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8532 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 178, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 41 162 324 73 22 36 65 146 274), lower := (rows 41 162 324 73 22 36 65 128 256), losses := [] }

theorem u8532 : Upper (D 6) (R 6) [40,160,320,65,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8533 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 2, region := 41, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 41 162 324 73 22 36 66 145 273), lower := (rows 41 162 324 73 22 36 66 128 256), losses := [] }

theorem u8533 : Upper (D 6) (R 6) [40,160,320,65,6,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8534 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 41 162 324 73 22 36 80 131 259), lower := (rows 41 162 324 73 22 36 80 128 256), losses := [] }

theorem u8534 : Upper (D 6) (R 6) [40,160,320,65,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8534 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8535 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 178, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 41 162 324 73 22 48 65 134 262), lower := (rows 41 162 324 73 22 48 65 128 256), losses := [] }

theorem u8535 : Upper (D 6) (R 6) [40,160,320,65,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8535 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8536 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 162 324 73 22 48 66 133 261), lower := (rows 41 162 324 73 22 48 66 128 256), losses := [] }

theorem u8536 : Upper (D 6) (R 6) [40,160,320,65,6,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8536 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8537 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 41 162 324 73 22 48 68 131 259), lower := (rows 41 162 324 73 22 48 68 128 256), losses := [] }

theorem u8537 : Upper (D 6) (R 6) [40,160,320,65,6,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8537 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8538 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 162, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 162 324 74 21 36 65 146 274), lower := (rows 41 162 324 74 21 36 65 128 256), losses := [] }

theorem u8538 : Upper (D 6) (R 6) [40,160,320,66,5,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8539 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 309, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 41 162 324 74 21 36 66 145 273), lower := (rows 41 162 324 74 21 36 66 128 256), losses := [] }

theorem u8539 : Upper (D 6) (R 6) [40,160,320,66,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8540 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 41 162 324 74 21 36 80 131 259), lower := (rows 41 162 324 74 21 36 80 128 256), losses := [] }

theorem u8540 : Upper (D 6) (R 6) [40,160,320,66,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8540 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8541 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 162 324 74 21 48 65 134 262), lower := (rows 41 162 324 74 21 48 65 128 256), losses := [] }

theorem u8541 : Upper (D 6) (R 6) [40,160,320,66,5,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8541 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8542 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 309, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 162 324 74 21 48 66 133 261), lower := (rows 41 162 324 74 21 48 66 128 256), losses := [] }

theorem u8542 : Upper (D 6) (R 6) [40,160,320,66,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8542 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8543 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 41 162 324 74 21 48 68 131 259), lower := (rows 41 162 324 74 21 48 68 128 256), losses := [] }

theorem u8543 : Upper (D 6) (R 6) [40,160,320,66,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8543 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8544 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(3,2)], upper := (rows 41 162 324 74 22 36 65 145 273), lower := (rows 41 162 324 74 22 36 65 128 256), losses := [{ target := 5, region := (rows 1 2 69 8 24 0 65 129 257), good := (rows 477 130 324 94 22 4 453 128 256) }] }

theorem u8544 : Upper (D 6) (R 6) [40,160,320,66,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8545 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 130, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 41 162 324 74 22 36 80 129 257), lower := (rows 41 162 324 74 22 36 80 128 256), losses := [] }

theorem u8545 : Upper (D 6) (R 6) [40,160,320,66,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8545 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8546 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 162 324 88 19 36 65 134 262), lower := (rows 41 162 324 88 19 36 65 128 256), losses := [] }

theorem u8546 : Upper (D 6) (R 6) [40,160,320,80,3,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8547 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 162 324 88 19 36 66 133 261), lower := (rows 41 162 324 88 19 36 66 128 256), losses := [] }

theorem u8547 : Upper (D 6) (R 6) [40,160,320,80,3,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8548 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 146, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 162 324 88 19 36 68 131 259), lower := (rows 41 162 324 88 19 36 68 128 256), losses := [] }

theorem u8548 : Upper (D 6) (R 6) [40,160,320,80,3,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8549 : PairBound 9 := { available := 48, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 194 324 11 21 36 66 176 304), lower := (rows 41 194 324 11 21 36 66 128 256), losses := [] }

theorem u8549 : Upper (D 6) (R 6) [40,192,320,3,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8550 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 194 324 11 21 36 80 162 290), lower := (rows 41 194 324 11 21 36 80 128 256), losses := [] }

theorem u8550 : Upper (D 6) (R 6) [40,192,320,3,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8550 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8551 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 8, region := 100, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 41 194 324 11 21 36 96 146 274), lower := (rows 41 194 324 11 21 36 96 128 256), losses := [] }

theorem u8551 : Upper (D 6) (R 6) [40,192,320,3,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8552 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 194 324 11 22 36 65 176 304), lower := (rows 41 194 324 11 22 36 65 128 256), losses := [] }

theorem u8552 : Upper (D 6) (R 6) [40,192,320,3,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8553 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 41 194 324 11 22 36 80 161 289), lower := (rows 41 194 324 11 22 36 80 128 256), losses := [] }

theorem u8553 : Upper (D 6) (R 6) [40,192,320,3,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8553 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8554 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,6),(2,0),(3,6)], upper := (rows 41 194 324 11 22 36 96 145 273), lower := (rows 41 194 324 11 22 36 96 128 256), losses := [] }

theorem u8554 : Upper (D 6) (R 6) [40,192,320,3,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8555 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 146, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 97 131 261 14 50 36 72 208 336), lower := (rows 97 131 261 14 50 36 72 128 256), losses := [] }

theorem u8555 : Upper (D 6) (R 6) [96,129,257,6,34,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8555 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8556 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 261 14 50 36 80 200 328), lower := (rows 97 131 261 14 50 36 80 128 256), losses := [] }

theorem u8556 : Upper (D 6) (R 6) [96,129,257,6,34,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8556 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8557 : Route 9 := (fun mask => (mask,id))

def c8557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8557 : Upper (D 6) (R 6) [96,129,257,18,36,2,4] 13 := by
  apply FastRouting.sound _ _ [96,129,257,18,36,2,4] 13 (by decide) (choices 1) [8,64] r8557 c8557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u657
  · exact u658

def b8558 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 276, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 97 131 261 26 52 34 72 196 324), lower := (rows 97 131 261 26 52 34 72 128 256), losses := [] }

theorem u8558 : Upper (D 6) (R 6) [96,129,257,18,36,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8558 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8559 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 6, region := 293, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 97 131 261 26 56 36 66 196 324), lower := (rows 97 131 261 26 56 36 66 128 256), losses := [] }

theorem u8559 : Upper (D 6) (R 6) [96,129,257,18,40,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8560 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 154, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 97 131 261 26 56 36 68 194 322), lower := (rows 97 131 261 26 56 36 68 128 256), losses := [] }

theorem u8560 : Upper (D 6) (R 6) [96,129,257,18,40,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8561 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 154, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 97 131 261 42 82 36 68 152 280), lower := (rows 97 131 261 42 82 36 68 128 256), losses := [] }

theorem u8561 : Upper (D 6) (R 6) [96,129,257,34,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8562 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 261 42 82 36 72 148 276), lower := (rows 97 131 261 42 82 36 72 128 256), losses := [] }

theorem u8562 : Upper (D 6) (R 6) [96,129,257,34,66,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8562 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8563 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 261 42 82 36 80 140 268), lower := (rows 97 131 261 42 82 36 80 128 256), losses := [] }

theorem u8563 : Upper (D 6) (R 6) [96,129,257,34,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8563 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8564 : Route 9 := (fun mask => (mask,id))

def c8564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8564 : Upper (D 6) (R 6) [96,129,257,34,68,4,2] 13 := by
  apply FastRouting.sound _ _ [96,129,257,34,68,4,2] 13 (by decide) (choices 1) [8,16] r8564 c8564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u659
  · exact u660

def b8565 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 261 42 84 36 72 146 274), lower := (rows 97 131 261 42 84 36 72 128 256), losses := [] }

theorem u8565 : Upper (D 6) (R 6) [96,129,257,34,68,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8565 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8566 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 261 42 84 36 80 138 266), lower := (rows 97 131 261 42 84 36 80 128 256), losses := [] }

theorem u8566 : Upper (D 6) (R 6) [96,129,257,34,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8566 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8567 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 80, targets := 33 },{ cop := 3, region := 65, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 97 131 261 42 88 36 66 148 276), lower := (rows 97 131 261 42 88 36 66 128 256), losses := [] }

theorem u8567 : Upper (D 6) (R 6) [96,129,257,34,72,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8568 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 154, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 97 131 261 42 88 36 68 146 274), lower := (rows 97 131 261 42 88 36 68 128 256), losses := [] }

theorem u8568 : Upper (D 6) (R 6) [96,129,257,34,72,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8569 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 81, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 97 131 261 42 88 36 80 134 262), lower := (rows 97 131 261 42 88 36 80 128 256), losses := [] }

theorem u8569 : Upper (D 6) (R 6) [96,129,257,34,72,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8569 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8570 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 130, targets := 4 },{ cop := 4, region := 356, targets := 1 }], pairs := [(1,2),(2,0)], upper := (rows 97 131 262 13 26 36 80 224 352), lower := (rows 97 131 262 13 26 36 80 128 256), losses := [] }

theorem u8570 : Upper (D 6) (R 6) [96,129,258,5,10,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8570 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8571 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 131 262 13 26 36 96 208 336), lower := (rows 97 131 262 13 26 36 96 128 256), losses := [] }

theorem u8571 : Upper (D 6) (R 6) [96,129,258,5,10,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8572 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 262 13 26 48 96 196 324), lower := (rows 97 131 262 13 26 48 96 128 256), losses := [] }

theorem u8572 : Upper (D 6) (R 6) [96,129,258,5,10,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8572 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8573 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 146, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 97 131 262 13 50 36 72 208 336), lower := (rows 97 131 262 13 50 36 72 128 256), losses := [] }

theorem u8573 : Upper (D 6) (R 6) [96,129,258,5,34,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8573 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8574 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 262 13 50 36 80 200 328), lower := (rows 97 131 262 13 50 36 80 128 256), losses := [] }

theorem u8574 : Upper (D 6) (R 6) [96,129,258,5,34,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8574 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8575 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 163, targets := 4 },{ cop := 1, region := 356, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 97 131 262 25 28 34 68 224 352), lower := (rows 97 131 262 25 28 34 68 128 256), losses := [] }

theorem u8575 : Upper (D 6) (R 6) [96,129,258,17,12,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8576 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 131 262 25 28 34 96 196 324), lower := (rows 97 131 262 25 28 34 96 128 256), losses := [] }

theorem u8576 : Upper (D 6) (R 6) [96,129,258,17,12,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8577 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 81, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 97 131 262 42 88 36 65 148 276), lower := (rows 97 131 262 42 88 36 65 128 256), losses := [] }

theorem u8577 : Upper (D 6) (R 6) [96,129,258,34,72,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8578 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 154, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 97 131 262 42 88 36 68 145 273), lower := (rows 97 131 262 42 88 36 68 128 256), losses := [] }

theorem u8578 : Upper (D 6) (R 6) [96,129,258,34,72,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8579 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 81, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 97 131 262 42 88 36 80 133 261), lower := (rows 97 131 262 42 88 36 80 128 256), losses := [] }

theorem u8579 : Upper (D 6) (R 6) [96,129,258,34,72,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8579 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8579
end Delivery.IrregularNine14.P06
