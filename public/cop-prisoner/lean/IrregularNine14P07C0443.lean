import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0159
import IrregularNine14P07C0160

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26580 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 266 84 11 176 33 194 194 450), lower := (rows 37 266 84 11 176 33 64 128 256), losses := [] }

theorem u26580 : Upper (D 7) (R 7) [36,264,80,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26581 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 37 266 84 11 176 34 193 193 449), lower := (rows 37 266 84 11 176 34 64 128 256), losses := [] }

theorem u26581 : Upper (D 7) (R 7) [36,264,80,3,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26582 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 11 176 96 195 131 387), lower := (rows 37 266 84 11 176 96 64 128 256), losses := [] }

theorem u26582 : Upper (D 7) (R 7) [36,264,80,3,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26583 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 84 11 176 160 67 195 323), lower := (rows 37 266 84 11 176 160 64 128 256), losses := [] }

theorem u26583 : Upper (D 7) (R 7) [36,264,80,3,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26584 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 37 266 84 42 19 33 192 192 448), lower := (rows 37 266 84 42 19 33 64 128 256), losses := [] }

theorem u26584 : Upper (D 7) (R 7) [36,264,80,34,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26585 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 42 19 96 193 129 385), lower := (rows 37 266 84 42 19 96 64 128 256), losses := [] }

theorem u26585 : Upper (D 7) (R 7) [36,264,80,34,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26586 : Route 9 := (fun mask => (mask,id))

def c26586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26586 : Upper (D 7) (R 7) [36,264,80,34,3,128] 13 := by
  apply FastRouting.sound _ _ [36,264,80,34,3,128] 13 (by decide) (choices 1) [1,128] r26586 c26586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9584
  · exact u9585

def b26587 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 266 84 42 145 33 194 194 450), lower := (rows 37 266 84 42 145 33 64 128 256), losses := [] }

theorem u26587 : Upper (D 7) (R 7) [36,264,80,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26588 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 42, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 266 84 42 145 34 193 193 449), lower := (rows 37 266 84 42 145 34 64 128 256), losses := [] }

theorem u26588 : Upper (D 7) (R 7) [36,264,80,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26589 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 42 145 96 195 131 387), lower := (rows 37 266 84 42 145 96 64 128 256), losses := [] }

theorem u26589 : Upper (D 7) (R 7) [36,264,80,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26590 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 266 84 42 145 160 67 195 323), lower := (rows 37 266 84 42 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 264 117 40 177 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 266 53 42 177 160 0 160 256) }] }

theorem u26590 : Upper (D 7) (R 7) [36,264,80,34,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26591 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 84 42 146 33 193 193 449), lower := (rows 37 266 84 42 146 33 64 128 256), losses := [] }

theorem u26591 : Upper (D 7) (R 7) [36,264,80,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26592 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 42 146 96 193 129 385), lower := (rows 37 266 84 42 146 96 64 128 256), losses := [] }

theorem u26592 : Upper (D 7) (R 7) [36,264,80,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26593 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 40, targets := 65 }], pairs := [(1,7),(3,0),(3,6),(3,7)], upper := (rows 37 266 84 42 146 160 65 193 321), lower := (rows 37 266 84 42 146 160 64 128 256), losses := [] }

theorem u26593 : Upper (D 7) (R 7) [36,264,80,34,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26594 : Route 9 := (fun mask => (mask,id))

def c26594 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26594 : Upper (D 7) (R 7) [36,264,80,65,129,2] 13 := by
  apply FastRouting.sound _ _ [36,264,80,65,129,2] 13 (by decide) (choices 1) [2,32,128] r26594 c26594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9586
  · exact u9587
  · exact u9588

def b26595 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(1,7),(3,7),(4,6)], upper := (rows 37 266 84 73 145 160 98 162 290), lower := (rows 37 266 84 73 145 160 64 128 256), losses := [] }

theorem u26595 : Upper (D 7) (R 7) [36,264,80,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26596 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 84 73 146 33 226 162 418), lower := (rows 37 266 84 73 146 33 64 128 256), losses := [] }

theorem u26596 : Upper (D 7) (R 7) [36,264,80,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26597 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(1,6),(3,1),(4,6)], upper := (rows 37 266 84 73 146 34 225 161 417), lower := (rows 37 266 84 73 146 34 64 128 256), losses := [{ target := 6, region := (rows 5 10 4 8 26 58 0 141 269), good := (rows 421 442 437 443 178 50 0 128 256) }] }

theorem u26597 : Upper (D 7) (R 7) [36,264,80,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26598 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(1,7),(3,7),(4,6)], upper := (rows 37 266 84 73 146 160 99 163 291), lower := (rows 37 266 84 73 146 160 64 128 256), losses := [] }

theorem u26598 : Upper (D 7) (R 7) [36,264,80,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26599 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 266 84 74 19 33 224 160 416), lower := (rows 37 266 84 74 19 33 64 128 256), losses := [] }

theorem u26599 : Upper (D 7) (R 7) [36,264,80,66,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26600 : Route 9 := (fun mask => (mask,id))

def c26600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26600 : Upper (D 7) (R 7) [36,264,80,66,3,128] 13 := by
  apply FastRouting.sound _ _ [36,264,80,66,3,128] 13 (by decide) (choices 1) [1,32,128] r26600 c26600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9589
  · exact u9590
  · exact u9591

def b26601 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 266 84 74 145 33 226 162 418), lower := (rows 37 266 84 74 145 33 64 128 256), losses := [] }

theorem u26601 : Upper (D 7) (R 7) [36,264,80,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26602 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,1),(2,1),(4,1),(4,6)], upper := (rows 37 266 84 74 145 34 225 161 417), lower := (rows 37 266 84 74 145 34 64 128 256), losses := [] }

theorem u26602 : Upper (D 7) (R 7) [36,264,80,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26603 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 266 84 74 145 160 99 163 291), lower := (rows 37 266 84 74 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 264 117 72 177 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 266 53 10 177 160 0 160 256) }] }

theorem u26603 : Upper (D 7) (R 7) [36,264,80,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26604 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 101, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 84 74 146 33 225 161 417), lower := (rows 37 266 84 74 146 33 64 128 256), losses := [] }

theorem u26604 : Upper (D 7) (R 7) [36,264,80,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26605 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(2,1),(3,7)], upper := (rows 37 266 84 74 146 160 97 161 289), lower := (rows 37 266 84 74 146 160 64 128 256), losses := [] }

theorem u26605 : Upper (D 7) (R 7) [36,264,80,66,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26606 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 266 84 74 176 33 195 131 387), lower := (rows 37 266 84 74 176 33 64 128 256), losses := [] }

theorem u26606 : Upper (D 7) (R 7) [36,264,80,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26607 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 37 266 84 74 176 34 193 129 385), lower := (rows 37 266 84 74 176 34 64 128 256), losses := [] }

theorem u26607 : Upper (D 7) (R 7) [36,264,80,66,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26608 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 84 74 176 160 67 131 259), lower := (rows 37 266 84 74 176 160 64 128 256), losses := [] }

theorem u26608 : Upper (D 7) (R 7) [36,264,80,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26609 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 84 104 19 33 194 130 386), lower := (rows 37 266 84 104 19 33 64 128 256), losses := [] }

theorem u26609 : Upper (D 7) (R 7) [36,264,80,96,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26610 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 196, targets := 34 },{ cop := 0, region := 200, targets := 2 }], pairs := [(2,1),(2,5),(3,0),(3,1)], upper := (rows 37 266 84 104 19 34 193 129 385), lower := (rows 37 266 84 104 19 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 50 64 128 256), good := (rows 44 298 124 104 50 34 64 128 256) }] }

theorem u26610 : Upper (D 7) (R 7) [36,264,80,96,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26611 : Route 9 := (fun mask => (mask,id))

def c26611 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26611 : Upper (D 7) (R 7) [36,264,80,96,3,128] 13 := by
  apply FastRouting.sound _ _ [36,264,80,96,3,128] 13 (by decide) (choices 1) [1,2,128] r26611 c26611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9592
  · exact u9593
  · exact u9594

def b26612 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 84 104 145 33 194 130 386), lower := (rows 37 266 84 104 145 33 64 128 256), losses := [] }

theorem u26612 : Upper (D 7) (R 7) [36,264,80,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26613 : Route 9 := (fun mask => (mask,id))

def c26613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26613 : Upper (D 7) (R 7) [36,264,80,96,129,2] 13 := by
  apply FastRouting.sound _ _ [36,264,80,96,129,2] 13 (by decide) (choices 1) [1,2,128] r26613 c26613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9595
  · exact u9596
  · exact u9597

def b26614 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(1,7),(3,0),(3,7)], upper := (rows 37 266 84 104 145 160 67 131 259), lower := (rows 37 266 84 104 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 176 64 128 256), good := (rows 44 266 124 104 176 160 64 160 256) },{ target := 1, region := (rows 5 0 4 12 16 176 64 128 256), good := (rows 45 264 125 104 177 160 64 160 256) }] }

theorem u26614 : Upper (D 7) (R 7) [36,264,80,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26615 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 84 104 146 33 195 131 387), lower := (rows 37 266 84 104 146 33 64 128 256), losses := [] }

theorem u26615 : Upper (D 7) (R 7) [36,264,80,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26616 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(0,7),(3,0),(3,1)], upper := (rows 37 266 84 104 146 34 193 129 385), lower := (rows 37 266 84 104 146 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 50 64 128 256), good := (rows 44 298 124 104 178 34 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 50 0 133 261), good := (rows 421 298 437 40 178 34 0 128 256) },{ target := 7, region := (rows 5 2 4 12 16 50 64 0 256), good := (rows 45 298 125 104 50 34 64 0 256) }] }

theorem u26616 : Upper (D 7) (R 7) [36,264,80,96,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26617 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(1,7),(3,0),(3,7)], upper := (rows 37 266 84 104 146 160 67 131 259), lower := (rows 37 266 84 104 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 176 64 128 256), good := (rows 44 266 124 104 178 160 64 160 256) },{ target := 1, region := (rows 5 0 4 12 16 176 64 128 256), good := (rows 45 264 125 104 176 160 64 160 256) }] }

theorem u26617 : Upper (D 7) (R 7) [36,264,80,96,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26618 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 200, targets := 2 },{ cop := 3, region := 354, targets := 1 },{ cop := 4, region := 228, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(3,1)], upper := (rows 37 266 84 137 19 34 224 224 480), lower := (rows 37 266 84 137 19 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 32 97 161 289), good := (rows 493 264 92 457 477 480 64 128 256) }] }

theorem u26618 : Upper (D 7) (R 7) [36,264,80,129,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26619 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 137 19 96 226 162 418), lower := (rows 37 266 84 137 19 96 64 128 256), losses := [] }

theorem u26619 : Upper (D 7) (R 7) [36,264,80,129,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26620 : Route 9 := (fun mask => (mask,id))

def c26620 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26620 : Upper (D 7) (R 7) [36,264,80,129,3,128] 13 := by
  apply FastRouting.sound _ _ [36,264,80,129,3,128] 13 (by decide) (choices 1) [2,32] r26620 c26620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9598
  · exact u9599

def b26621 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 266 84 137 50 33 194 194 450), lower := (rows 37 266 84 137 50 33 64 128 256), losses := [] }

theorem u26621 : Upper (D 7) (R 7) [36,264,80,129,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26622 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 266 84 137 50 34 193 193 449), lower := (rows 37 266 84 137 50 34 64 128 256), losses := [] }

theorem u26622 : Upper (D 7) (R 7) [36,264,80,129,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26623 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 137 50 96 195 131 387), lower := (rows 37 266 84 137 50 96 64 128 256), losses := [] }

theorem u26623 : Upper (D 7) (R 7) [36,264,80,129,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26624 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 4, region := 69, targets := 128 }], pairs := [(0,7),(1,5),(2,7),(3,5)], upper := (rows 37 266 84 137 50 160 67 195 323), lower := (rows 37 266 84 137 50 160 64 128 256), losses := [] }

theorem u26624 : Upper (D 7) (R 7) [36,264,80,129,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26625 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 354, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 266 84 137 146 33 98 226 354), lower := (rows 37 266 84 137 146 33 64 128 256), losses := [] }

theorem u26625 : Upper (D 7) (R 7) [36,264,80,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26626 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 0, region := 200, targets := 2 },{ cop := 3, region := 354, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 37 266 84 137 146 34 97 225 353), lower := (rows 37 266 84 137 146 34 64 128 256), losses := [] }

theorem u26626 : Upper (D 7) (R 7) [36,264,80,129,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26627 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 137 146 96 99 163 291), lower := (rows 37 266 84 137 146 96 64 128 256), losses := [] }

theorem u26627 : Upper (D 7) (R 7) [36,264,80,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26628 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 266 84 137 176 33 66 194 322), lower := (rows 37 266 84 137 176 33 64 128 256), losses := [] }

theorem u26628 : Upper (D 7) (R 7) [36,264,80,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26629 : Route 9 := (fun mask => (mask,id))

def c26629 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26629 : Upper (D 7) (R 7) [36,264,80,129,160,2] 13 := by
  apply FastRouting.sound _ _ [36,264,80,129,160,2] 13 (by decide) (choices 1) [1,2] r26629 c26629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9600
  · exact u9601

def b26630 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 137 176 96 67 131 259), lower := (rows 37 266 84 137 176 96 64 128 256), losses := [] }

theorem u26630 : Upper (D 7) (R 7) [36,264,80,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26631 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 37 266 84 138 19 33 224 224 480), lower := (rows 37 266 84 138 19 33 64 128 256), losses := [] }

theorem u26631 : Upper (D 7) (R 7) [36,264,80,130,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26632 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 138 19 96 225 161 417), lower := (rows 37 266 84 138 19 96 64 128 256), losses := [] }

theorem u26632 : Upper (D 7) (R 7) [36,264,80,130,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26633 : Route 9 := (fun mask => (mask,id))

def c26633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26633 : Upper (D 7) (R 7) [36,264,80,130,3,128] 13 := by
  apply FastRouting.sound _ _ [36,264,80,130,3,128] 13 (by decide) (choices 1) [1,32] r26633 c26633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9602
  · exact u9603

def b26634 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 266 84 138 145 33 98 226 354), lower := (rows 37 266 84 138 145 33 64 128 256), losses := [] }

theorem u26634 : Upper (D 7) (R 7) [36,264,80,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26635 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 213, targets := 2 }], pairs := [(0,1),(2,1),(2,7),(4,1)], upper := (rows 37 266 84 138 145 34 97 225 353), lower := (rows 37 266 84 138 145 34 64 128 256), losses := [{ target := 7, region := (rows 1 2 20 8 16 42 65 0 257), good := (rows 357 298 84 42 341 34 64 0 256) }] }

theorem u26635 : Upper (D 7) (R 7) [36,264,80,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26636 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 138 145 96 99 163 291), lower := (rows 37 266 84 138 145 96 64 128 256), losses := [] }

theorem u26636 : Upper (D 7) (R 7) [36,264,80,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26637 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 266 84 138 176 33 67 195 323), lower := (rows 37 266 84 138 176 33 64 128 256), losses := [] }

theorem u26637 : Upper (D 7) (R 7) [36,264,80,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26638 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 37 266 84 138 176 34 65 193 321), lower := (rows 37 266 84 138 176 34 64 128 256), losses := [] }

theorem u26638 : Upper (D 7) (R 7) [36,264,80,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26639 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 138 176 96 67 131 259), lower := (rows 37 266 84 138 176 96 64 128 256), losses := [] }

theorem u26639 : Upper (D 7) (R 7) [36,264,80,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26639
end Delivery.IrregularNine14.P07
