import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0011

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8520 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 14 265 81 48 192 162 290), lower := (rows 37 194 14 265 81 48 192 128 256), losses := [] }

theorem u8520 : Upper (D 7) (R 7) [36,192,10,257,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8520 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8521 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 424, targets := 66 },{ cop := 4, region := 162, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,1),(3,6)], upper := (rows 37 194 14 265 81 160 66 176 304), lower := (rows 37 194 14 265 81 160 66 128 256), losses := [] }

theorem u8521 : Upper (D 7) (R 7) [36,192,10,257,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8522 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 194 14 265 81 160 80 162 290), lower := (rows 37 194 14 265 81 160 80 128 256), losses := [] }

theorem u8522 : Upper (D 7) (R 7) [36,192,10,257,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8522 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8523 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 194 14 265 81 160 96 146 274), lower := (rows 37 194 14 265 81 160 96 128 256), losses := [] }

theorem u8523 : Upper (D 7) (R 7) [36,192,10,257,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8524 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 194 14 280 81 160 65 162 290), lower := (rows 37 194 14 280 81 160 65 128 256), losses := [] }

theorem u8524 : Upper (D 7) (R 7) [36,192,10,272,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8525 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 4, region := 424, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 194 14 280 81 160 66 161 289), lower := (rows 37 194 14 280 81 160 66 128 256), losses := [] }

theorem u8525 : Upper (D 7) (R 7) [36,192,10,272,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8526 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 194 14 280 81 160 96 131 259), lower := (rows 37 194 14 280 81 160 96 128 256), losses := [] }

theorem u8526 : Upper (D 7) (R 7) [36,192,10,272,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8527 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 66, targets := 32 }], pairs := [(0,6),(1,5),(4,6)], upper := (rows 37 194 14 328 145 48 65 162 290), lower := (rows 37 194 14 328 145 48 65 128 256), losses := [] }

theorem u8527 : Upper (D 7) (R 7) [36,192,10,320,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8527 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8528 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 194 14 328 145 48 66 161 289), lower := (rows 37 194 14 328 145 48 66 128 256), losses := [] }

theorem u8528 : Upper (D 7) (R 7) [36,192,10,320,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8528 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8529 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 37 194 14 328 145 48 96 131 259), lower := (rows 37 194 14 328 145 48 96 128 256), losses := [] }

theorem u8529 : Upper (D 7) (R 7) [36,192,10,320,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8529 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8530 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 84, targets := 160 }], pairs := [(2,5),(2,7),(4,5),(4,7)], upper := (rows 37 194 28 11 81 160 66 416 288), lower := (rows 37 194 28 11 81 160 66 128 256), losses := [] }

theorem u8530 : Upper (D 7) (R 7) [36,192,24,3,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8531 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 194 28 11 81 160 96 386 258), lower := (rows 37 194 28 11 81 160 96 128 256), losses := [] }

theorem u8531 : Upper (D 7) (R 7) [36,192,24,3,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8532 : Route 9 := (fun mask => (mask,id))

def c8532 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8532 : Upper (D 7) (R 7) [36,192,24,3,65,128,256] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,65,128,256] 13 (by decide) (choices 1) [2,32] r8532 c8532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u676
  · exact u677

def b8533 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 84, targets := 160 }], pairs := [(2,5),(2,7),(4,5)], upper := (rows 37 194 28 11 81 288 66 160 416), lower := (rows 37 194 28 11 81 288 66 128 256), losses := [] }

theorem u8533 : Upper (D 7) (R 7) [36,192,24,3,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8533 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8534 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 142, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 28 11 81 288 96 130 386), lower := (rows 37 194 28 11 81 288 96 128 256), losses := [] }

theorem u8534 : Upper (D 7) (R 7) [36,192,24,3,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8534 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8535 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 28 11 81 288 192 162 290), lower := (rows 37 194 28 11 81 288 192 128 256), losses := [] }

theorem u8535 : Upper (D 7) (R 7) [36,192,24,3,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8535 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8536 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 0, region := 194, targets := 1 },{ cop := 7, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 37 194 28 11 273 96 66 160 416), lower := (rows 37 194 28 11 273 96 66 128 256), losses := [] }

theorem u8536 : Upper (D 7) (R 7) [36,192,24,3,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8537 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6)], upper := (rows 37 194 28 11 273 96 96 130 386), lower := (rows 37 194 28 11 273 96 96 128 256), losses := [] }

theorem u8537 : Upper (D 7) (R 7) [36,192,24,3,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8538 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 28 11 273 96 192 162 290), lower := (rows 37 194 28 11 273 96 192 128 256), losses := [] }

theorem u8538 : Upper (D 7) (R 7) [36,192,24,3,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8539 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 2, region := 97, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(3,5)], upper := (rows 37 194 28 11 304 96 65 130 386), lower := (rows 37 194 28 11 304 96 65 128 256), losses := [] }

theorem u8539 : Upper (D 7) (R 7) [36,192,24,3,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8540 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5),(3,5),(4,1),(4,6)], upper := (rows 37 194 28 11 304 96 66 129 385), lower := (rows 37 194 28 11 304 96 66 128 256), losses := [] }

theorem u8540 : Upper (D 7) (R 7) [36,192,24,3,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8541 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 28 11 304 96 192 131 259), lower := (rows 37 194 28 11 304 96 192 128 256), losses := [] }

theorem u8541 : Upper (D 7) (R 7) [36,192,24,3,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8542 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 434, targets := 1 }], pairs := [(0,6),(1,0),(2,0),(4,0)], upper := (rows 37 194 28 11 336 160 65 162 290), lower := (rows 37 194 28 11 336 160 65 128 256), losses := [{ target := 0, region := (rows 0 82 12 8 82 255 64 222 350), good := (rows 420 498 446 446 498 160 498 160 256) },{ target := 6, region := (rows 5 2 4 8 16 174 0 138 266), good := (rows 37 418 445 427 272 160 1 160 256) }] }

theorem u8542 : Upper (D 7) (R 7) [36,192,24,3,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8543 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 5, region := 66, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(0,1),(0,6),(1,0),(1,5)], upper := (rows 37 194 28 11 336 160 66 161 289), lower := (rows 37 194 28 11 336 160 66 128 256), losses := [] }

theorem u8543 : Upper (D 7) (R 7) [36,192,24,3,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8544 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 66, targets := 1 }], pairs := [(0,6),(1,0),(2,7),(4,7)], upper := (rows 37 194 28 11 336 160 96 131 259), lower := (rows 37 194 28 11 336 160 96 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 174 0 136 264), good := (rows 37 162 445 427 272 160 32 160 256) },{ target := 7, region := (rows 1 2 12 8 24 32 97 0 264), good := (rows 101 66 284 351 336 96 96 0 256) }] }

theorem u8544 : Upper (D 7) (R 7) [36,192,24,3,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8545 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 85, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 28 42 81 288 65 130 386), lower := (rows 37 194 28 42 81 288 65 128 256), losses := [] }

theorem u8545 : Upper (D 7) (R 7) [36,192,24,34,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8545 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8546 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 194 28 42 81 288 66 129 385), lower := (rows 37 194 28 42 81 288 66 128 256), losses := [] }

theorem u8546 : Upper (D 7) (R 7) [36,192,24,34,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8546 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8547 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 28 42 81 288 192 131 259), lower := (rows 37 194 28 42 81 288 192 128 256), losses := [] }

theorem u8547 : Upper (D 7) (R 7) [36,192,24,34,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8547 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8548 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 78, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 28 73 145 288 66 162 290), lower := (rows 37 194 28 73 145 288 66 128 256), losses := [] }

theorem u8548 : Upper (D 7) (R 7) [36,192,24,65,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8548 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8549 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 28 73 145 288 96 130 258), lower := (rows 37 194 28 73 145 288 96 128 256), losses := [] }

theorem u8549 : Upper (D 7) (R 7) [36,192,24,65,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8549 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8550 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 28 73 176 288 65 130 258), lower := (rows 37 194 28 73 176 288 65 128 256), losses := [] }

theorem u8550 : Upper (D 7) (R 7) [36,192,24,65,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8550 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8551 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(3,5)], upper := (rows 37 194 28 73 176 288 66 131 259), lower := (rows 37 194 28 73 176 288 66 128 256), losses := [] }

theorem u8551 : Upper (D 7) (R 7) [36,192,24,65,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8551 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8552 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 0, region := 194, targets := 1 },{ cop := 7, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 37 194 28 73 273 34 66 160 416), lower := (rows 37 194 28 73 273 34 66 128 256), losses := [] }

theorem u8552 : Upper (D 7) (R 7) [36,192,24,65,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8553 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 194 28 73 273 34 96 130 386), lower := (rows 37 194 28 73 273 34 96 128 256), losses := [] }

theorem u8553 : Upper (D 7) (R 7) [36,192,24,65,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8554 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 28 73 273 34 192 162 290), lower := (rows 37 194 28 73 273 34 192 128 256), losses := [] }

theorem u8554 : Upper (D 7) (R 7) [36,192,24,65,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8555 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 194, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(3,5)], upper := (rows 37 194 28 73 273 160 66 162 290), lower := (rows 37 194 28 73 273 160 66 128 256), losses := [{ target := 5, region := (rows 1 162 20 25 16 0 227 128 256), good := (rows 79 194 28 73 349 194 66 194 256) }] }

theorem u8555 : Upper (D 7) (R 7) [36,192,24,65,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8556 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 194 28 73 273 160 96 130 258), lower := (rows 37 194 28 73 273 160 96 128 256), losses := [] }

theorem u8556 : Upper (D 7) (R 7) [36,192,24,65,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8557 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(4,0)], upper := (rows 37 194 28 73 274 34 65 160 416), lower := (rows 37 194 28 73 274 34 65 128 256), losses := [] }

theorem u8557 : Upper (D 7) (R 7) [36,192,24,65,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8558 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,5)], upper := (rows 37 194 28 73 274 34 96 129 385), lower := (rows 37 194 28 73 274 34 96 128 256), losses := [] }

theorem u8558 : Upper (D 7) (R 7) [36,192,24,65,258,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8559 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 28 73 274 34 192 161 289), lower := (rows 37 194 28 73 274 34 192 128 256), losses := [] }

theorem u8559 : Upper (D 7) (R 7) [36,192,24,65,258,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8560 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 194 28 73 274 160 65 162 290), lower := (rows 37 194 28 73 274 160 65 128 256), losses := [] }

theorem u8560 : Upper (D 7) (R 7) [36,192,24,65,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8561 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 5, region := 66, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(0,1),(0,6),(1,0),(1,5)], upper := (rows 37 194 28 73 274 160 66 161 289), lower := (rows 37 194 28 73 274 160 66 128 256), losses := [] }

theorem u8561 : Upper (D 7) (R 7) [36,192,24,65,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8562 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 194 28 73 274 160 96 131 259), lower := (rows 37 194 28 73 274 160 96 128 256), losses := [] }

theorem u8562 : Upper (D 7) (R 7) [36,192,24,65,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8563 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 28 73 304 34 65 130 386), lower := (rows 37 194 28 73 304 34 65 128 256), losses := [] }

theorem u8563 : Upper (D 7) (R 7) [36,192,24,65,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8564 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5),(3,5),(4,1),(4,6)], upper := (rows 37 194 28 73 304 34 66 129 385), lower := (rows 37 194 28 73 304 34 66 128 256), losses := [] }

theorem u8564 : Upper (D 7) (R 7) [36,192,24,65,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8565 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 28 73 304 34 192 131 259), lower := (rows 37 194 28 73 304 34 192 128 256), losses := [] }

theorem u8565 : Upper (D 7) (R 7) [36,192,24,65,288,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8566 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 28 73 304 160 65 130 258), lower := (rows 37 194 28 73 304 160 65 128 256), losses := [] }

theorem u8566 : Upper (D 7) (R 7) [36,192,24,65,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8567 : Route 9 := (fun mask => (mask,id))

def c8567 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8567 : Upper (D 7) (R 7) [36,192,24,65,288,128,2] 13 := by
  apply FastRouting.sound _ _ [36,192,24,65,288,128,2] 13 (by decide) (choices 1) [1,2] r8567 c8567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u678
  · exact u679

def b8568 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 194 28 73 400 34 65 162 290), lower := (rows 37 194 28 73 400 34 65 128 256), losses := [] }

theorem u8568 : Upper (D 7) (R 7) [36,192,24,65,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8569 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 4, region := 66, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 37 194 28 73 400 34 66 161 289), lower := (rows 37 194 28 73 400 34 66 128 256), losses := [] }

theorem u8569 : Upper (D 7) (R 7) [36,192,24,65,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8570 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 194 28 73 400 34 96 131 259), lower := (rows 37 194 28 73 400 34 96 128 256), losses := [] }

theorem u8570 : Upper (D 7) (R 7) [36,192,24,65,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8571 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 293, targets := 2 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,1),(1,0),(2,1)], upper := (rows 37 194 69 25 26 288 66 160 416), lower := (rows 37 194 69 25 26 288 66 128 256), losses := [] }

theorem u8571 : Upper (D 7) (R 7) [36,192,65,17,10,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8571 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8572 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 69 25 26 288 96 130 386), lower := (rows 37 194 69 25 26 288 96 128 256), losses := [] }

theorem u8572 : Upper (D 7) (R 7) [36,192,65,17,10,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8572 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8573 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 25 26 288 192 162 290), lower := (rows 37 194 69 25 26 288 192 128 256), losses := [] }

theorem u8573 : Upper (D 7) (R 7) [36,192,65,17,10,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8573 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8574 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 25 274 40 66 160 416), lower := (rows 37 194 69 25 274 40 66 128 256), losses := [] }

theorem u8574 : Upper (D 7) (R 7) [36,192,65,17,258,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8574 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8575 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 109, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 69 25 274 40 96 130 386), lower := (rows 37 194 69 25 274 40 96 128 256), losses := [] }

theorem u8575 : Upper (D 7) (R 7) [36,192,65,17,258,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8575 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8576 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 25 274 40 192 162 290), lower := (rows 37 194 69 25 274 40 192 128 256), losses := [] }

theorem u8576 : Upper (D 7) (R 7) [36,192,65,17,258,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8576 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8577 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 194 69 25 400 40 66 162 290), lower := (rows 37 194 69 25 400 40 66 128 256), losses := [] }

theorem u8577 : Upper (D 7) (R 7) [36,192,65,17,384,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8577 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8578 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 109, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 69 25 400 40 96 130 258), lower := (rows 37 194 69 25 400 40 96 128 256), losses := [] }

theorem u8578 : Upper (D 7) (R 7) [36,192,65,17,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8578 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8579 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 26 56 288 65 130 386), lower := (rows 37 194 69 26 56 288 65 128 256), losses := [] }

theorem u8579 : Upper (D 7) (R 7) [36,192,65,18,40,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8579 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8579
end Delivery.IrregularNine14.P07
