import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9540 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(1,6),(4,6)], upper := (rows 37 266 70 88 146 160 65 161 289), lower := (rows 37 266 70 88 146 160 65 128 256), losses := [{ target := 6, region := (rows 5 10 4 8 28 253 0 197 325), good := (rows 437 314 439 442 178 160 417 160 256) }] }

theorem u9540 : Upper (D 7) (R 7) [36,264,66,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9541 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 108, targets := 1 }], pairs := [(0,6),(2,0),(3,0),(4,6)], upper := (rows 37 266 70 88 146 160 96 129 257), lower := (rows 37 266 70 88 146 160 96 128 256), losses := [] }

theorem u9541 : Upper (D 7) (R 7) [36,264,66,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9542 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 266 70 104 145 48 65 130 386), lower := (rows 37 266 70 104 145 48 65 128 256), losses := [] }

theorem u9542 : Upper (D 7) (R 7) [36,264,66,96,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9542 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9543 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 266 70 104 145 48 66 129 385), lower := (rows 37 266 70 104 145 48 66 128 256), losses := [] }

theorem u9543 : Upper (D 7) (R 7) [36,264,66,96,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9543 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9544 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 70 104 145 48 192 131 259), lower := (rows 37 266 70 104 145 48 192 128 256), losses := [] }

theorem u9544 : Upper (D 7) (R 7) [36,264,66,96,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9544 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9545 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(3,7),(4,6)], upper := (rows 37 266 70 104 145 160 65 146 274), lower := (rows 37 266 70 104 145 160 65 128 256), losses := [] }

theorem u9545 : Upper (D 7) (R 7) [36,264,66,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9546 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 70 104 145 160 66 145 273), lower := (rows 37 266 70 104 145 160 66 128 256), losses := [] }

theorem u9546 : Upper (D 7) (R 7) [36,264,66,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9547 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 70 104 145 160 80 131 259), lower := (rows 37 266 70 104 145 160 80 128 256), losses := [] }

theorem u9547 : Upper (D 7) (R 7) [36,264,66,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9547 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9548 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(3,7),(4,6)], upper := (rows 37 266 70 104 146 160 65 145 273), lower := (rows 37 266 70 104 146 160 65 128 256), losses := [] }

theorem u9548 : Upper (D 7) (R 7) [36,264,66,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9549 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 70 104 146 160 80 129 257), lower := (rows 37 266 70 104 146 160 80 128 256), losses := [] }

theorem u9549 : Upper (D 7) (R 7) [36,264,66,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9549 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9550 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 4, region := 68, targets := 32 }], pairs := [(0,1),(2,5),(3,1)], upper := (rows 37 266 70 137 19 160 80 224 352), lower := (rows 37 266 70 137 19 160 80 128 256), losses := [] }

theorem u9550 : Upper (D 7) (R 7) [36,264,66,129,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9550 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9551 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 228, targets := 1 },{ cop := 4, region := 232, targets := 2 }], pairs := [(1,7),(2,0),(2,7),(3,1)], upper := (rows 37 266 70 137 19 160 96 208 336), lower := (rows 37 266 70 137 19 160 96 128 256), losses := [{ target := 7, region := (rows 1 10 28 8 24 32 97 0 280), good := (rows 101 286 70 351 343 96 96 0 256) }] }

theorem u9551 : Upper (D 7) (R 7) [36,264,66,129,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9552 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 70 137 81 160 66 176 304), lower := (rows 37 266 70 137 81 160 66 128 256), losses := [] }

theorem u9552 : Upper (D 7) (R 7) [36,264,66,129,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9553 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 266 70 137 81 160 80 162 290), lower := (rows 37 266 70 137 81 160 80 128 256), losses := [] }

theorem u9553 : Upper (D 7) (R 7) [36,264,66,129,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9553 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9554 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 266 70 137 81 160 96 146 274), lower := (rows 37 266 70 137 81 160 96 128 256), losses := [] }

theorem u9554 : Upper (D 7) (R 7) [36,264,66,129,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9555 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 2, region := 176, targets := 1 }], pairs := [(2,5),(4,0),(4,1),(4,7)], upper := (rows 37 266 70 137 112 160 65 146 274), lower := (rows 37 266 70 137 112 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 6 8 16 0 73 128 256), good := (rows 69 334 70 201 80 128 65 128 256) }] }

theorem u9555 : Upper (D 7) (R 7) [36,264,66,129,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9556 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 70 137 112 160 66 145 273), lower := (rows 37 266 70 137 112 160 66 128 256), losses := [] }

theorem u9556 : Upper (D 7) (R 7) [36,264,66,129,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9557 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 70 137 112 160 80 131 259), lower := (rows 37 266 70 137 112 160 80 128 256), losses := [] }

theorem u9557 : Upper (D 7) (R 7) [36,264,66,129,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9557 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9558 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 185, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 37 266 70 137 208 33 66 176 304), lower := (rows 37 266 70 137 208 33 66 128 256), losses := [] }

theorem u9558 : Upper (D 7) (R 7) [36,264,66,129,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9559 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 70 137 208 33 80 162 290), lower := (rows 37 266 70 137 208 33 80 128 256), losses := [] }

theorem u9559 : Upper (D 7) (R 7) [36,264,66,129,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9559 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9560 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 2, region := 144, targets := 33 }], pairs := [(0,7),(2,7),(4,0),(4,5)], upper := (rows 37 266 70 137 208 33 96 146 274), lower := (rows 37 266 70 137 208 33 96 128 256), losses := [] }

theorem u9560 : Upper (D 7) (R 7) [36,264,66,129,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9561 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 176, targets := 1 }], pairs := [(1,6),(3,6),(4,0)], upper := (rows 37 266 70 137 208 48 65 162 290), lower := (rows 37 266 70 137 208 48 65 128 256), losses := [] }

theorem u9561 : Upper (D 7) (R 7) [36,264,66,129,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9561 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9562 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 266 70 137 208 48 66 161 289), lower := (rows 37 266 70 137 208 48 66 128 256), losses := [] }

theorem u9562 : Upper (D 7) (R 7) [36,264,66,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9562 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9563 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 37 266 70 137 208 48 96 131 259), lower := (rows 37 266 70 137 208 48 96 128 256), losses := [] }

theorem u9563 : Upper (D 7) (R 7) [36,264,66,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9563 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9564 : Route 9 := (fun mask => (mask,id))

def c9564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9564 : Upper (D 7) (R 7) [36,264,66,130,96,128,1] 13 := by
  apply FastRouting.sound _ _ [36,264,66,130,96,128,1] 13 (by decide) (choices 1) [1,16] r9564 c9564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u745
  · exact u746

def b9565 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 70 138 112 160 80 129 257), lower := (rows 37 266 70 138 112 160 80 128 256), losses := [] }

theorem u9565 : Upper (D 7) (R 7) [36,264,66,130,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9565 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9566 : Route 9 := (fun mask => (mask,id))

def c9566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9566 : Upper (D 7) (R 7) [36,264,66,130,129,16,1] 13 := by
  apply FastRouting.sound _ _ [36,264,66,130,129,16,1] 13 (by decide) (choices 1) [32,64] r9566 c9566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u747
  · exact u748

def r9567 : Route 9 := (fun mask => (mask,id))

def c9567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u9567 : Upper (D 7) (R 7) [36,264,66,130,129,16,32] 13 := by
  apply FastRouting.sound _ _ [36,264,66,130,129,16,32] 13 (by decide) (choices 1) [1,64] r9567 c9567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u749
  · exact u750

def b9568 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 68, targets := 160 },{ cop := 2, region := 161, targets := 2 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,1),(2,5),(2,7),(3,1)], upper := (rows 37 266 70 152 19 160 65 224 352), lower := (rows 37 266 70 152 19 160 65 128 256), losses := [] }

theorem u9568 : Upper (D 7) (R 7) [36,264,66,144,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9569 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 161, targets := 2 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,1),(1,7),(2,0),(3,1)], upper := (rows 37 266 70 152 19 160 96 193 321), lower := (rows 37 266 70 152 19 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 22 8 16 168 235 128 256), good := (rows 100 366 70 252 86 224 96 224 256) },{ target := 7, region := (rows 1 10 20 8 16 32 97 0 273), good := (rows 357 266 70 286 343 96 96 0 256) }] }

theorem u9569 : Upper (D 7) (R 7) [36,264,66,144,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9570 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 266 70 152 81 160 65 162 290), lower := (rows 37 266 70 152 81 160 65 128 256), losses := [] }

theorem u9570 : Upper (D 7) (R 7) [36,264,66,144,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9571 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 70 152 81 160 66 161 289), lower := (rows 37 266 70 152 81 160 66 128 256), losses := [] }

theorem u9571 : Upper (D 7) (R 7) [36,264,66,144,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9572 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 266 70 152 81 160 96 131 259), lower := (rows 37 266 70 152 81 160 96 128 256), losses := [] }

theorem u9572 : Upper (D 7) (R 7) [36,264,66,144,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9573 : Route 9 := (fun mask => (mask,id))

def c9573 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9573 : Upper (D 7) (R 7) [36,264,66,144,96,128,1] 13 := by
  apply FastRouting.sound _ _ [36,264,66,144,96,128,1] 13 (by decide) (choices 1) [1,2] r9573 c9573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u751
  · exact u752

def b9574 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 70 152 112 160 66 129 257), lower := (rows 37 266 70 152 112 160 66 128 256), losses := [] }

theorem u9574 : Upper (D 7) (R 7) [36,264,66,144,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9575 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 2, region := 144, targets := 33 }], pairs := [(0,7),(2,7),(4,0),(4,5)], upper := (rows 37 266 70 168 208 33 65 146 274), lower := (rows 37 266 70 168 208 33 65 128 256), losses := [] }

theorem u9575 : Upper (D 7) (R 7) [36,264,66,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9576 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 185, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 37 266 70 168 208 33 66 145 273), lower := (rows 37 266 70 168 208 33 66 128 256), losses := [] }

theorem u9576 : Upper (D 7) (R 7) [36,264,66,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9577 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 70 168 208 33 80 131 259), lower := (rows 37 266 70 168 208 33 80 128 256), losses := [] }

theorem u9577 : Upper (D 7) (R 7) [36,264,66,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9577 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9578 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 68, targets := 160 }], pairs := [(0,6),(2,5),(2,7),(4,6)], upper := (rows 37 266 70 200 19 160 65 176 304), lower := (rows 37 266 70 200 19 160 65 128 256), losses := [] }

theorem u9578 : Upper (D 7) (R 7) [36,264,66,192,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9579 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 266 70 200 19 160 80 161 289), lower := (rows 37 266 70 200 19 160 80 128 256), losses := [] }

theorem u9579 : Upper (D 7) (R 7) [36,264,66,192,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9579 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9580 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(0,6),(3,0),(3,1),(4,6)], upper := (rows 37 266 70 200 19 160 96 145 273), lower := (rows 37 266 70 200 19 160 96 128 256), losses := [] }

theorem u9580 : Upper (D 7) (R 7) [36,264,66,192,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9581 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 72, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 37 266 70 200 145 48 65 162 290), lower := (rows 37 266 70 200 145 48 65 128 256), losses := [] }

theorem u9581 : Upper (D 7) (R 7) [36,264,66,192,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9581 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9582 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 266 70 200 145 48 66 161 289), lower := (rows 37 266 70 200 145 48 66 128 256), losses := [] }

theorem u9582 : Upper (D 7) (R 7) [36,264,66,192,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9582 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9583 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 104, targets := 1 }], pairs := [(0,6),(3,0),(4,6)], upper := (rows 37 266 70 200 145 48 96 131 259), lower := (rows 37 266 70 200 145 48 96 128 256), losses := [] }

theorem u9583 : Upper (D 7) (R 7) [36,264,66,192,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9583 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9584 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 2, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 266 84 42 19 160 65 192 448), lower := (rows 37 266 84 42 19 160 65 128 256), losses := [] }

theorem u9584 : Upper (D 7) (R 7) [36,264,80,34,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9585 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 4, region := 196, targets := 32 }], pairs := [(0,1),(0,6),(2,1),(2,5)], upper := (rows 37 266 84 42 19 160 192 193 321), lower := (rows 37 266 84 42 19 160 192 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 224 0 128 256), good := (rows 37 266 53 42 19 160 160 160 256) }] }

theorem u9585 : Upper (D 7) (R 7) [36,264,80,34,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9586 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 3, region := 418, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,1),(4,6)], upper := (rows 37 266 84 73 145 34 66 160 416), lower := (rows 37 266 84 73 145 34 66 128 256), losses := [] }

theorem u9586 : Upper (D 7) (R 7) [36,264,80,65,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9587 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 266 84 73 145 34 96 130 386), lower := (rows 37 266 84 73 145 34 96 128 256), losses := [] }

theorem u9587 : Upper (D 7) (R 7) [36,264,80,65,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9588 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 266 84 73 145 34 192 162 290), lower := (rows 37 266 84 73 145 34 192 128 256), losses := [] }

theorem u9588 : Upper (D 7) (R 7) [36,264,80,65,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9589 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 37 266 84 74 19 160 65 160 416), lower := (rows 37 266 84 74 19 160 65 128 256), losses := [] }

theorem u9589 : Upper (D 7) (R 7) [36,264,80,66,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9590 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(2,0),(2,1)], upper := (rows 37 266 84 74 19 160 96 129 385), lower := (rows 37 266 84 74 19 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 160 225 128 256), good := (rows 100 266 92 74 94 224 96 224 256) }] }

theorem u9590 : Upper (D 7) (R 7) [36,264,80,66,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9591 : Route 9 := (fun mask => (mask,id))

def c9591 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9591 : Upper (D 7) (R 7) [36,264,80,66,3,128,128] 13 := by
  apply FastRouting.sound _ _ [36,264,80,66,3,128,128] 13 (by decide) (choices 1) [1,32] r9591 c9591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u753
  · exact u754

def b9592 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 2, region := 426, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(3,7)], upper := (rows 37 266 84 104 19 160 65 130 386), lower := (rows 37 266 84 104 19 160 65 128 256), losses := [] }

theorem u9592 : Upper (D 7) (R 7) [36,264,80,96,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9593 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 4, region := 68, targets := 129 }], pairs := [(0,1),(2,0),(2,7),(3,1)], upper := (rows 37 266 84 104 19 160 66 129 385), lower := (rows 37 266 84 104 19 160 66 128 256), losses := [] }

theorem u9593 : Upper (D 7) (R 7) [36,264,80,96,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9594 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 266 84 104 19 160 192 131 259), lower := (rows 37 266 84 104 19 160 192 128 256), losses := [] }

theorem u9594 : Upper (D 7) (R 7) [36,264,80,96,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9595 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 68, targets := 162 },{ cop := 0, region := 72, targets := 2 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 37 266 84 104 145 34 65 130 386), lower := (rows 37 266 84 104 145 34 65 128 256), losses := [] }

theorem u9595 : Upper (D 7) (R 7) [36,264,80,96,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9596 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 266 84 104 145 34 66 129 385), lower := (rows 37 266 84 104 145 34 66 128 256), losses := [] }

theorem u9596 : Upper (D 7) (R 7) [36,264,80,96,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9597 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 37 266 84 104 145 34 192 131 259), lower := (rows 37 266 84 104 145 34 192 128 256), losses := [] }

theorem u9597 : Upper (D 7) (R 7) [36,264,80,96,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9598 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 4, region := 68, targets := 160 }], pairs := [(0,1),(2,5),(2,7),(3,1)], upper := (rows 37 266 84 137 19 160 66 224 352), lower := (rows 37 266 84 137 19 160 66 128 256), losses := [] }

theorem u9598 : Upper (D 7) (R 7) [36,264,80,129,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9599 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 354, targets := 1 },{ cop := 4, region := 228, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(2,1)], upper := (rows 37 266 84 137 19 160 96 194 322), lower := (rows 37 266 84 137 19 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 168 235 128 256), good := (rows 101 360 84 233 85 224 96 224 256) },{ target := 7, region := (rows 1 10 28 8 24 32 97 0 280), good := (rows 101 286 340 351 343 96 96 0 256) }] }

theorem u9599 : Upper (D 7) (R 7) [36,264,80,129,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9599
end Delivery.IrregularNine14.P07
