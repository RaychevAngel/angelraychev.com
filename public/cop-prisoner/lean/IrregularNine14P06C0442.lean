import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0138

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26520 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 131 292 25 82 36 70 198 326), lower := (rows 41 131 292 25 82 36 64 128 256), losses := [] }

theorem u26520 : Upper (D 6) (R 6) [40,129,288,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26521 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 292 25 82 96 70 134 262), lower := (rows 41 131 292 25 82 96 64 128 256), losses := [] }

theorem u26521 : Upper (D 6) (R 6) [40,129,288,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26522 : Route 9 := (fun mask => (mask,id))

def c26522 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26522 : Upper (D 6) (R 6) [40,129,288,17,68,2] 13 := by
  apply FastRouting.sound _ _ [40,129,288,17,68,2] 13 (by decide) (choices 1) [2,4] r26522 c26522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8283
  · exact u8284

def b26523 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 292 25 84 36 66 194 322), lower := (rows 41 131 292 25 84 36 64 128 256), losses := [] }

theorem u26523 : Upper (D 6) (R 6) [40,129,288,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26524 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 292 25 84 96 70 134 262), lower := (rows 41 131 292 25 84 96 64 128 256), losses := [] }

theorem u26524 : Upper (D 6) (R 6) [40,129,288,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26525 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 292 26 81 34 68 196 324), lower := (rows 41 131 292 26 81 34 64 128 256), losses := [] }

theorem u26525 : Upper (D 6) (R 6) [40,129,288,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26526 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 131 292 26 81 36 70 198 326), lower := (rows 41 131 292 26 81 36 64 128 256), losses := [] }

theorem u26526 : Upper (D 6) (R 6) [40,129,288,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26527 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 356, targets := 1 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 41 131 292 26 81 96 70 134 262), lower := (rows 41 131 292 26 81 96 64 128 256), losses := [] }

theorem u26527 : Upper (D 6) (R 6) [40,129,288,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26528 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 292 26 84 33 70 198 326), lower := (rows 41 131 292 26 84 33 64 128 256), losses := [] }

theorem u26528 : Upper (D 6) (R 6) [40,129,288,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26529 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 292 26 84 34 69 197 325), lower := (rows 41 131 292 26 84 34 64 128 256), losses := [] }

theorem u26529 : Upper (D 6) (R 6) [40,129,288,18,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26530 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 131 292 26 84 36 67 195 323), lower := (rows 41 131 292 26 84 36 64 128 256), losses := [] }

theorem u26530 : Upper (D 6) (R 6) [40,129,288,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26531 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 41 131 292 26 84 96 71 135 263), lower := (rows 41 131 292 26 84 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 112 64 128 256), good := (rows 41 129 292 57 116 96 96 128 256) }] }

theorem u26531 : Upper (D 6) (R 6) [40,129,288,18,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26532 : Route 9 := (fun mask => (mask,id))

def c26532 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26532 : Upper (D 6) (R 6) [40,129,288,20,65,2] 13 := by
  apply FastRouting.sound _ _ [40,129,288,20,65,2] 13 (by decide) (choices 1) [2,4] r26532 c26532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8285
  · exact u8286

def b26533 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 131 292 28 81 36 66 194 322), lower := (rows 41 131 292 28 81 36 64 128 256), losses := [] }

theorem u26533 : Upper (D 6) (R 6) [40,129,288,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26534 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 356, targets := 1 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 41 131 292 28 81 96 70 134 262), lower := (rows 41 131 292 28 81 96 64 128 256), losses := [] }

theorem u26534 : Upper (D 6) (R 6) [40,129,288,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26535 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 292 28 82 33 70 198 326), lower := (rows 41 131 292 28 82 33 64 128 256), losses := [] }

theorem u26535 : Upper (D 6) (R 6) [40,129,288,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26536 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 41 131 292 28 82 34 69 197 325), lower := (rows 41 131 292 28 82 34 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 50 64 128 256), good := (rows 41 163 288 57 114 34 64 128 256) },{ target := 6, region := (rows 9 2 4 8 16 50 0 128 256), good := (rows 41 163 292 61 50 34 0 128 256) }] }

theorem u26536 : Upper (D 6) (R 6) [40,129,288,20,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26537 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 131 292 28 82 36 67 195 323), lower := (rows 41 131 292 28 82 36 64 128 256), losses := [] }

theorem u26537 : Upper (D 6) (R 6) [40,129,288,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26538 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 41 131 292 28 82 96 71 135 263), lower := (rows 41 131 292 28 82 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 112 64 128 256), good := (rows 41 129 292 61 112 96 96 128 256) }] }

theorem u26538 : Upper (D 6) (R 6) [40,129,288,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26539 : Route 9 := (fun mask => (mask,id))

def c26539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26539 : Upper (D 6) (R 6) [40,129,288,65,6,2] 13 := by
  apply FastRouting.sound _ _ [40,129,288,65,6,2] 13 (by decide) (choices 1) [4,16] r26539 c26539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8287
  · exact u8288

def b26540 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 131 292 73 22 36 82 210 338), lower := (rows 41 131 292 73 22 36 64 128 256), losses := [] }

theorem u26540 : Upper (D 6) (R 6) [40,129,288,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26541 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 41 131 292 73 22 48 70 198 326), lower := (rows 41 131 292 73 22 48 64 128 256), losses := [] }

theorem u26541 : Upper (D 6) (R 6) [40,129,288,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26541 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26542 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 292 73 22 96 86 150 278), lower := (rows 41 131 292 73 22 96 64 128 256), losses := [] }

theorem u26542 : Upper (D 6) (R 6) [40,129,288,65,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26543 : Route 9 := (fun mask => (mask,id))

def c26543 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26543 : Upper (D 6) (R 6) [40,129,288,65,68,2] 13 := by
  apply FastRouting.sound _ _ [40,129,288,65,68,2] 13 (by decide) (choices 1) [2,4,16] r26543 c26543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8289
  · exact u8290
  · exact u8291

def b26544 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 131 292 73 84 36 82 146 274), lower := (rows 41 131 292 73 84 36 64 128 256), losses := [] }

theorem u26544 : Upper (D 6) (R 6) [40,129,288,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26545 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 292 73 84 48 70 134 262), lower := (rows 41 131 292 73 84 48 64 128 256), losses := [] }

theorem u26545 : Upper (D 6) (R 6) [40,129,288,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26545 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26546 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 292 74 21 34 84 212 340), lower := (rows 41 131 292 74 21 34 64 128 256), losses := [] }

theorem u26546 : Upper (D 6) (R 6) [40,129,288,66,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26547 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 41 131 292 74 21 36 82 210 338), lower := (rows 41 131 292 74 21 36 64 128 256), losses := [] }

theorem u26547 : Upper (D 6) (R 6) [40,129,288,66,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26548 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 41 131 292 74 21 48 70 198 326), lower := (rows 41 131 292 74 21 48 64 128 256), losses := [] }

theorem u26548 : Upper (D 6) (R 6) [40,129,288,66,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26548 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26549 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 292 74 21 96 86 150 278), lower := (rows 41 131 292 74 21 96 64 128 256), losses := [] }

theorem u26549 : Upper (D 6) (R 6) [40,129,288,66,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26550 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 292 74 22 33 84 212 340), lower := (rows 41 131 292 74 22 33 64 128 256), losses := [] }

theorem u26550 : Upper (D 6) (R 6) [40,129,288,66,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26551 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 131 292 74 22 36 81 209 337), lower := (rows 41 131 292 74 22 36 64 128 256), losses := [] }

theorem u26551 : Upper (D 6) (R 6) [40,129,288,66,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26552 : Route 9 := (fun mask => (mask,id))

def c26552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26552 : Upper (D 6) (R 6) [40,129,288,66,6,16] 13 := by
  apply FastRouting.sound _ _ [40,129,288,66,6,16] 13 (by decide) (choices 1) [1,4] r26552 c26552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8292
  · exact u8293

def b26553 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 292 74 22 96 85 149 277), lower := (rows 41 131 292 74 22 96 64 128 256), losses := [] }

theorem u26553 : Upper (D 6) (R 6) [40,129,288,66,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26554 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 292 74 81 34 84 148 276), lower := (rows 41 131 292 74 81 34 64 128 256), losses := [] }

theorem u26554 : Upper (D 6) (R 6) [40,129,288,66,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26555 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 131 292 74 81 36 86 150 278), lower := (rows 41 131 292 74 81 36 64 128 256), losses := [] }

theorem u26555 : Upper (D 6) (R 6) [40,129,288,66,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26556 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 292 74 81 48 70 134 262), lower := (rows 41 131 292 74 81 48 64 128 256), losses := [] }

theorem u26556 : Upper (D 6) (R 6) [40,129,288,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26556 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26557 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 292 74 84 33 86 150 278), lower := (rows 41 131 292 74 84 33 64 128 256), losses := [] }

theorem u26557 : Upper (D 6) (R 6) [40,129,288,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26558 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 292 74 84 34 85 149 277), lower := (rows 41 131 292 74 84 34 64 128 256), losses := [] }

theorem u26558 : Upper (D 6) (R 6) [40,129,288,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26559 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 131 292 74 84 36 83 147 275), lower := (rows 41 131 292 74 84 36 64 128 256), losses := [] }

theorem u26559 : Upper (D 6) (R 6) [40,129,288,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26560 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 41 131 292 74 84 48 71 135 263), lower := (rows 41 131 292 74 84 48 64 128 256), losses := [] }

theorem u26560 : Upper (D 6) (R 6) [40,129,288,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26560 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26561 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 292 76 22 33 82 210 338), lower := (rows 41 131 292 76 22 33 64 128 256), losses := [] }

theorem u26561 : Upper (D 6) (R 6) [40,129,288,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26562 : Route 9 := (fun mask => (mask,id))

def c26562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26562 : Upper (D 6) (R 6) [40,129,288,68,6,2] 13 := by
  apply FastRouting.sound _ _ [40,129,288,68,6,2] 13 (by decide) (choices 1) [1,16] r26562 c26562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8294
  · exact u8295

def b26563 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 194, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 41 131 292 76 22 48 67 195 323), lower := (rows 41 131 292 76 22 48 64 128 256), losses := [] }

theorem u26563 : Upper (D 6) (R 6) [40,129,288,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26563 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26564 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 292 76 22 96 83 147 275), lower := (rows 41 131 292 76 22 96 64 128 256), losses := [] }

theorem u26564 : Upper (D 6) (R 6) [40,129,288,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26565 : Route 9 := (fun mask => (mask,id))

def c26565 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26565 : Upper (D 6) (R 6) [40,129,288,68,65,2] 13 := by
  apply FastRouting.sound _ _ [40,129,288,68,65,2] 13 (by decide) (choices 1) [2,4,16] r26565 c26565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8296
  · exact u8297
  · exact u8298

def b26566 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 131 292 76 81 36 82 146 274), lower := (rows 41 131 292 76 81 36 64 128 256), losses := [] }

theorem u26566 : Upper (D 6) (R 6) [40,129,288,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26567 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 292 76 81 48 70 134 262), lower := (rows 41 131 292 76 81 48 64 128 256), losses := [] }

theorem u26567 : Upper (D 6) (R 6) [40,129,288,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26567 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26568 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 292 76 82 33 86 150 278), lower := (rows 41 131 292 76 82 33 64 128 256), losses := [] }

theorem u26568 : Upper (D 6) (R 6) [40,129,288,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26569 : Route 9 := (fun mask => (mask,id))

def c26569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26569 : Upper (D 6) (R 6) [40,129,288,68,66,2] 13 := by
  apply FastRouting.sound _ _ [40,129,288,68,66,2] 13 (by decide) (choices 1) [1,4,16] r26569 c26569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8299
  · exact u8300
  · exact u8301

def b26570 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 131 292 76 82 36 83 147 275), lower := (rows 41 131 292 76 82 36 64 128 256), losses := [] }

theorem u26570 : Upper (D 6) (R 6) [40,129,288,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26571 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 41 131 292 76 82 48 71 135 263), lower := (rows 41 131 292 76 82 48 64 128 256), losses := [] }

theorem u26571 : Upper (D 6) (R 6) [40,129,288,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26571 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26572 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 292 88 22 33 70 198 326), lower := (rows 41 131 292 88 22 33 64 128 256), losses := [] }

theorem u26572 : Upper (D 6) (R 6) [40,129,288,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26573 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 41 131 292 88 22 34 69 197 325), lower := (rows 41 131 292 88 22 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 37 24 16 32 67 131 259), good := (rows 493 453 292 88 476 484 64 128 256) },{ target := 2, region := (rows 9 2 0 8 16 50 64 128 256), good := (rows 41 163 288 121 50 34 64 128 256) }] }

theorem u26573 : Upper (D 6) (R 6) [40,129,288,80,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26574 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 131 292 88 22 36 67 195 323), lower := (rows 41 131 292 88 22 36 64 128 256), losses := [] }

theorem u26574 : Upper (D 6) (R 6) [40,129,288,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26575 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 292 88 22 96 71 135 263), lower := (rows 41 131 292 88 22 96 64 128 256), losses := [] }

theorem u26575 : Upper (D 6) (R 6) [40,129,288,80,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26576 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 41 131 324 13 22 34 112 240 368), lower := (rows 41 131 324 13 22 34 64 128 256), losses := [] }

theorem u26576 : Upper (D 6) (R 6) [40,129,320,5,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26577 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 131 324 13 22 48 98 226 354), lower := (rows 41 131 324 13 22 48 64 128 256), losses := [] }

theorem u26577 : Upper (D 6) (R 6) [40,129,320,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26577 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26578 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 41, targets := 2 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 41 131 324 13 22 96 114 178 306), lower := (rows 41 131 324 13 22 96 64 128 256), losses := [] }

theorem u26578 : Upper (D 6) (R 6) [40,129,320,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26579 : Route 9 := (fun mask => (mask,id))

def c26579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26579 : Upper (D 6) (R 6) [40,129,320,5,66,2] 13 := by
  apply FastRouting.sound _ _ [40,129,320,5,66,2] 13 (by decide) (choices 1) [4,16,32] r26579 c26579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8302
  · exact u8303
  · exact u8304

#print axioms u26579
end Delivery.IrregularNine14.P06
