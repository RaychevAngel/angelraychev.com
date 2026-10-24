import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0159

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r26520 : Route 9 := (fun mask => (mask,id))

def c26520 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26520 : Upper (D 7) (R 7) [36,264,66,129,192,16] 13 := by
  apply FastRouting.sound _ _ [36,264,66,129,192,16] 13 (by decide) (choices 1) [1,2,32] r26520 c26520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9561
  · exact u9562
  · exact u9563

def b26521 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 49, targets := 2 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 266 70 138 112 33 209 145 401), lower := (rows 37 266 70 138 112 33 64 128 256), losses := [] }

theorem u26521 : Upper (D 7) (R 7) [36,264,66,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26522 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 70 138 112 48 193 129 385), lower := (rows 37 266 70 138 112 48 64 128 256), losses := [] }

theorem u26522 : Upper (D 7) (R 7) [36,264,66,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26522 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26523 : Route 9 := (fun mask => (mask,id))

def c26523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26523 : Upper (D 7) (R 7) [36,264,66,130,96,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,130,96,128] 13 (by decide) (choices 1) [1,16] r26523 c26523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9564
  · exact u9565

def b26524 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 266 70 138 145 33 112 240 368), lower := (rows 37 266 70 138 145 33 64 128 256), losses := [] }

theorem u26524 : Upper (D 7) (R 7) [36,264,66,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26525 : Route 9 := (fun mask => (mask,id))

def c26525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26525 : Upper (D 7) (R 7) [36,264,66,130,129,16] 13 := by
  apply FastRouting.sound _ _ [36,264,66,130,129,16] 13 (by decide) (choices 1) [1,32] r26525 c26525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9566
  · exact u9567

def b26526 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 138 145 96 113 177 305), lower := (rows 37 266 70 138 145 96 64 128 256), losses := [] }

theorem u26526 : Upper (D 7) (R 7) [36,264,66,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26527 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 266 70 138 176 33 81 209 337), lower := (rows 37 266 70 138 176 33 64 128 256), losses := [] }

theorem u26527 : Upper (D 7) (R 7) [36,264,66,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26528 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 70 138 176 48 65 193 321), lower := (rows 37 266 70 138 176 48 64 128 256), losses := [] }

theorem u26528 : Upper (D 7) (R 7) [36,264,66,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26528 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26529 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 138 176 96 81 145 273), lower := (rows 37 266 70 138 176 96 64 128 256), losses := [] }

theorem u26529 : Upper (D 7) (R 7) [36,264,66,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26530 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 266 70 138 208 33 113 177 305), lower := (rows 37 266 70 138 208 33 64 128 256), losses := [] }

theorem u26530 : Upper (D 7) (R 7) [36,264,66,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26531 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(1,6),(3,6)], upper := (rows 37 266 70 138 208 48 97 161 289), lower := (rows 37 266 70 138 208 48 64 128 256), losses := [] }

theorem u26531 : Upper (D 7) (R 7) [36,264,66,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26531 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26532 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 266 70 152 19 33 224 224 480), lower := (rows 37 266 70 152 19 33 64 128 256), losses := [] }

theorem u26532 : Upper (D 7) (R 7) [36,264,66,144,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26533 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 152 19 96 225 161 417), lower := (rows 37 266 70 152 19 96 64 128 256), losses := [] }

theorem u26533 : Upper (D 7) (R 7) [36,264,66,144,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26534 : Route 9 := (fun mask => (mask,id))

def c26534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26534 : Upper (D 7) (R 7) [36,264,66,144,3,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,144,3,128] 13 (by decide) (choices 1) [1,32] r26534 c26534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9568
  · exact u9569

def b26535 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 266 70 152 50 33 193 193 449), lower := (rows 37 266 70 152 50 33 64 128 256), losses := [] }

theorem u26535 : Upper (D 7) (R 7) [36,264,66,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26536 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 152 50 96 193 129 385), lower := (rows 37 266 70 152 50 96 64 128 256), losses := [] }

theorem u26536 : Upper (D 7) (R 7) [36,264,66,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26537 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 69, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,0)], upper := (rows 37 266 70 152 50 160 65 193 321), lower := (rows 37 266 70 152 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 168 64 128 256), good := (rows 36 314 86 184 50 160 64 160 256) }] }

theorem u26537 : Upper (D 7) (R 7) [36,264,66,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26538 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 266 70 152 81 33 226 162 418), lower := (rows 37 266 70 152 81 33 64 128 256), losses := [] }

theorem u26538 : Upper (D 7) (R 7) [36,264,66,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26539 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 37 266 70 152 81 34 225 161 417), lower := (rows 37 266 70 152 81 34 64 128 256), losses := [] }

theorem u26539 : Upper (D 7) (R 7) [36,264,66,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26540 : Route 9 := (fun mask => (mask,id))

def c26540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26540 : Upper (D 7) (R 7) [36,264,66,144,65,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,144,65,128] 13 (by decide) (choices 1) [1,2,32] r26540 c26540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9570
  · exact u9571
  · exact u9572

def b26541 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 266 70 152 112 33 195 131 387), lower := (rows 37 266 70 152 112 33 64 128 256), losses := [] }

theorem u26541 : Upper (D 7) (R 7) [36,264,66,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26542 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 37 266 70 152 112 34 193 129 385), lower := (rows 37 266 70 152 112 34 64 128 256), losses := [] }

theorem u26542 : Upper (D 7) (R 7) [36,264,66,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26543 : Route 9 := (fun mask => (mask,id))

def c26543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26543 : Upper (D 7) (R 7) [36,264,66,144,96,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,144,96,128] 13 (by decide) (choices 1) [1,2] r26543 c26543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9573
  · exact u9574

def b26544 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 266 70 168 19 33 208 208 464), lower := (rows 37 266 70 168 19 33 64 128 256), losses := [] }

theorem u26544 : Upper (D 7) (R 7) [36,264,66,160,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26545 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 266 70 168 19 48 193 193 449), lower := (rows 37 266 70 168 19 48 64 128 256), losses := [] }

theorem u26545 : Upper (D 7) (R 7) [36,264,66,160,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26545 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26546 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 168 19 96 209 145 401), lower := (rows 37 266 70 168 19 96 64 128 256), losses := [] }

theorem u26546 : Upper (D 7) (R 7) [36,264,66,160,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26547 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 266 70 168 19 160 81 209 337), lower := (rows 37 266 70 168 19 160 64 128 256), losses := [] }

theorem u26547 : Upper (D 7) (R 7) [36,264,66,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26548 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 266 70 168 81 33 210 146 402), lower := (rows 37 266 70 168 81 33 64 128 256), losses := [] }

theorem u26548 : Upper (D 7) (R 7) [36,264,66,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26549 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 37 266 70 168 81 34 209 145 401), lower := (rows 37 266 70 168 81 34 64 128 256), losses := [] }

theorem u26549 : Upper (D 7) (R 7) [36,264,66,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26550 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 266 70 168 81 48 195 131 387), lower := (rows 37 266 70 168 81 48 64 128 256), losses := [] }

theorem u26550 : Upper (D 7) (R 7) [36,264,66,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26550 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26551 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 266 70 168 81 160 83 147 275), lower := (rows 37 266 70 168 81 160 64 128 256), losses := [] }

theorem u26551 : Upper (D 7) (R 7) [36,264,66,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26552 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 40, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(3,1)], upper := (rows 37 266 70 168 145 33 82 210 338), lower := (rows 37 266 70 168 145 33 64 128 256), losses := [] }

theorem u26552 : Upper (D 7) (R 7) [36,264,66,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26553 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 266 70 168 145 34 81 209 337), lower := (rows 37 266 70 168 145 34 64 128 256), losses := [] }

theorem u26553 : Upper (D 7) (R 7) [36,264,66,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26554 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 70 168 145 48 67 195 323), lower := (rows 37 266 70 168 145 48 64 128 256), losses := [] }

theorem u26554 : Upper (D 7) (R 7) [36,264,66,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26554 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26555 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 168 145 96 83 147 275), lower := (rows 37 266 70 168 145 96 64 128 256), losses := [] }

theorem u26555 : Upper (D 7) (R 7) [36,264,66,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26556 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 266 70 168 146 33 81 209 337), lower := (rows 37 266 70 168 146 33 64 128 256), losses := [] }

theorem u26556 : Upper (D 7) (R 7) [36,264,66,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26557 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 70 168 146 48 65 193 321), lower := (rows 37 266 70 168 146 48 64 128 256), losses := [] }

theorem u26557 : Upper (D 7) (R 7) [36,264,66,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26557 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26558 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 168 146 96 81 145 273), lower := (rows 37 266 70 168 146 96 64 128 256), losses := [] }

theorem u26558 : Upper (D 7) (R 7) [36,264,66,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26559 : Route 9 := (fun mask => (mask,id))

def c26559 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26559 : Upper (D 7) (R 7) [36,264,66,160,192,1] 13 := by
  apply FastRouting.sound _ _ [36,264,66,160,192,1] 13 (by decide) (choices 1) [1,2,16] r26559 c26559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9575
  · exact u9576
  · exact u9577

def b26560 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 266 70 168 208 34 81 145 273), lower := (rows 37 266 70 168 208 34 64 128 256), losses := [] }

theorem u26560 : Upper (D 7) (R 7) [36,264,66,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26561 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 70 168 208 48 67 131 259), lower := (rows 37 266 70 168 208 48 64 128 256), losses := [] }

theorem u26561 : Upper (D 7) (R 7) [36,264,66,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26561 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26562 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 266 70 200 19 33 240 176 432), lower := (rows 37 266 70 200 19 33 64 128 256), losses := [] }

theorem u26562 : Upper (D 7) (R 7) [36,264,66,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26563 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 266 70 200 19 48 225 161 417), lower := (rows 37 266 70 200 19 48 64 128 256), losses := [] }

theorem u26563 : Upper (D 7) (R 7) [36,264,66,192,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26563 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26564 : Route 9 := (fun mask => (mask,id))

def c26564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26564 : Upper (D 7) (R 7) [36,264,66,192,3,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,192,3,128] 13 (by decide) (choices 1) [1,16,32] r26564 c26564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9578
  · exact u9579
  · exact u9580

def b26565 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 266 70 200 50 33 209 145 401), lower := (rows 37 266 70 200 50 33 64 128 256), losses := [] }

theorem u26565 : Upper (D 7) (R 7) [36,264,66,192,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26566 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 70 200 50 48 193 129 385), lower := (rows 37 266 70 200 50 48 64 128 256), losses := [] }

theorem u26566 : Upper (D 7) (R 7) [36,264,66,192,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26566 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26567 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 69, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 37 266 70 200 50 160 81 145 273), lower := (rows 37 266 70 200 50 160 64 128 256), losses := [] }

theorem u26567 : Upper (D 7) (R 7) [36,264,66,192,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26568 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 266 70 200 145 33 114 178 306), lower := (rows 37 266 70 200 145 33 64 128 256), losses := [] }

theorem u26568 : Upper (D 7) (R 7) [36,264,66,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26569 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 266 70 200 145 34 113 177 305), lower := (rows 37 266 70 200 145 34 64 128 256), losses := [] }

theorem u26569 : Upper (D 7) (R 7) [36,264,66,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26570 : Route 9 := (fun mask => (mask,id))

def c26570 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26570 : Upper (D 7) (R 7) [36,264,66,192,129,16] 13 := by
  apply FastRouting.sound _ _ [36,264,66,192,129,16] 13 (by decide) (choices 1) [1,2,32] r26570 c26570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9581
  · exact u9582
  · exact u9583

def b26571 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 266 70 200 176 33 83 147 275), lower := (rows 37 266 70 200 176 33 64 128 256), losses := [] }

theorem u26571 : Upper (D 7) (R 7) [36,264,66,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26572 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 266 70 200 176 34 81 145 273), lower := (rows 37 266 70 200 176 34 64 128 256), losses := [] }

theorem u26572 : Upper (D 7) (R 7) [36,264,66,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26573 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 70 200 176 48 67 131 259), lower := (rows 37 266 70 200 176 48 64 128 256), losses := [] }

theorem u26573 : Upper (D 7) (R 7) [36,264,66,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26573 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26574 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 266 84 11 145 34 224 224 480), lower := (rows 37 266 84 11 145 34 64 128 256), losses := [] }

theorem u26574 : Upper (D 7) (R 7) [36,264,80,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26575 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 11 145 96 226 162 418), lower := (rows 37 266 84 11 145 96 64 128 256), losses := [] }

theorem u26575 : Upper (D 7) (R 7) [36,264,80,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26576 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,7)], upper := (rows 37 266 84 11 145 160 98 226 354), lower := (rows 37 266 84 11 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 264 117 9 177 160 64 160 256) }] }

theorem u26576 : Upper (D 7) (R 7) [36,264,80,3,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26577 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 84 11 146 33 224 224 480), lower := (rows 37 266 84 11 146 33 64 128 256), losses := [] }

theorem u26577 : Upper (D 7) (R 7) [36,264,80,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26578 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 11 146 96 225 161 417), lower := (rows 37 266 84 11 146 96 64 128 256), losses := [] }

theorem u26578 : Upper (D 7) (R 7) [36,264,80,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26579 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(2,1),(3,7)], upper := (rows 37 266 84 11 146 160 97 225 353), lower := (rows 37 266 84 11 146 160 64 128 256), losses := [] }

theorem u26579 : Upper (D 7) (R 7) [36,264,80,3,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26579
end Delivery.IrregularNine14.P07
