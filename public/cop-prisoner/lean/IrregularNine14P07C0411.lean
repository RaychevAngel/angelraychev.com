import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0138

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r24660 : Route 9 := (fun mask => (mask,id))

def c24660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24660 : Upper (D 7) (R 7) [36,96,264,80,130,1] 13 := by
  apply FastRouting.sound _ _ [36,96,264,80,130,1] 13 (by decide) (choices 1) [1,2,128] r24660 c24660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8281
  · exact u8282
  · exact u8283

def b24661 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 268 88 146 34 193 129 385), lower := (rows 37 98 268 88 146 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 141 269), good := (rows 421 34 397 445 178 34 0 128 256) }] }

theorem u24661 : Upper (D 7) (R 7) [36,96,264,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24662 : Route 9 := (fun mask => (mask,id))

def c24662 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24662 : Upper (D 7) (R 7) [36,96,264,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,80,130,128] 13 (by decide) (choices 1) [1,2] r24662 c24662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8284
  · exact u8285

def b24663 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 268 137 19 34 208 208 464), lower := (rows 37 98 268 137 19 34 64 128 256), losses := [] }

theorem u24663 : Upper (D 7) (R 7) [36,96,264,129,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24664 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 37 98 268 137 19 48 194 194 450), lower := (rows 37 98 268 137 19 48 64 128 256), losses := [] }

theorem u24664 : Upper (D 7) (R 7) [36,96,264,129,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24664 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24665 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 268 137 19 96 210 146 402), lower := (rows 37 98 268 137 19 96 64 128 256), losses := [] }

theorem u24665 : Upper (D 7) (R 7) [36,96,264,129,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24666 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,7),(2,5),(3,5),(4,7)], upper := (rows 37 98 268 137 19 160 82 210 338), lower := (rows 37 98 268 137 19 160 64 128 256), losses := [] }

theorem u24666 : Upper (D 7) (R 7) [36,96,264,129,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24667 : Route 9 := (fun mask => (mask,id))

def c24667 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24667 : Upper (D 7) (R 7) [36,96,264,129,65,2] 13 := by
  apply FastRouting.sound _ _ [36,96,264,129,65,2] 13 (by decide) (choices 1) [2,16,128] r24667 c24667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8286
  · exact u8287
  · exact u8288

def b24668 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 268 137 81 48 194 130 386), lower := (rows 37 98 268 137 81 48 64 128 256), losses := [] }

theorem u24668 : Upper (D 7) (R 7) [36,96,264,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24668 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24669 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 162, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 268 137 81 160 82 146 274), lower := (rows 37 98 268 137 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 301 169 81 160 64 160 256) }] }

theorem u24669 : Upper (D 7) (R 7) [36,96,264,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24670 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 268 137 146 33 82 210 338), lower := (rows 37 98 268 137 146 33 64 128 256), losses := [] }

theorem u24670 : Upper (D 7) (R 7) [36,96,264,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24671 : Route 9 := (fun mask => (mask,id))

def c24671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24671 : Upper (D 7) (R 7) [36,96,264,129,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,264,129,130,2] 13 (by decide) (choices 1) [1,16] r24671 c24671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8289
  · exact u8290

def r24672 : Route 9 := (fun mask => (mask,id))

def c24672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24672 : Upper (D 7) (R 7) [36,96,264,129,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,264,129,130,16] 13 (by decide) (choices 1) [1,2] r24672 c24672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8291
  · exact u8292

def b24673 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 268 137 146 96 83 147 275), lower := (rows 37 98 268 137 146 96 64 128 256), losses := [] }

theorem u24673 : Upper (D 7) (R 7) [36,96,264,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24674 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 268 137 208 33 82 146 274), lower := (rows 37 98 268 137 208 33 64 128 256), losses := [] }

theorem u24674 : Upper (D 7) (R 7) [36,96,264,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24675 : Route 9 := (fun mask => (mask,id))

def c24675 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24675 : Upper (D 7) (R 7) [36,96,264,129,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,264,129,192,2] 13 (by decide) (choices 1) [1,2,16] r24675 c24675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8293
  · exact u8294
  · exact u8295

def b24676 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 268 137 208 48 67 131 259), lower := (rows 37 98 268 137 208 48 64 128 256), losses := [] }

theorem u24676 : Upper (D 7) (R 7) [36,96,264,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24676 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24677 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 268 138 19 33 208 208 464), lower := (rows 37 98 268 138 19 33 64 128 256), losses := [] }

theorem u24677 : Upper (D 7) (R 7) [36,96,264,130,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24678 : Route 9 := (fun mask => (mask,id))

def c24678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24678 : Upper (D 7) (R 7) [36,96,264,130,3,16] 13 := by
  apply FastRouting.sound _ _ [36,96,264,130,3,16] 13 (by decide) (choices 1) [1,128] r24678 c24678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8296
  · exact u8297

def b24679 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 268 138 19 96 209 145 401), lower := (rows 37 98 268 138 19 96 64 128 256), losses := [] }

theorem u24679 : Upper (D 7) (R 7) [36,96,264,130,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24680 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,7),(2,5),(3,5),(4,7)], upper := (rows 37 98 268 138 19 160 81 209 337), lower := (rows 37 98 268 138 19 160 64 128 256), losses := [] }

theorem u24680 : Upper (D 7) (R 7) [36,96,264,130,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24681 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 34, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 268 138 81 33 210 146 402), lower := (rows 37 98 268 138 81 33 64 128 256), losses := [] }

theorem u24681 : Upper (D 7) (R 7) [36,96,264,130,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24682 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 37 98 268 138 81 34 209 145 401), lower := (rows 37 98 268 138 81 34 64 128 256), losses := [] }

theorem u24682 : Upper (D 7) (R 7) [36,96,264,130,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24683 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 268 138 81 48 195 131 387), lower := (rows 37 98 268 138 81 48 64 128 256), losses := [] }

theorem u24683 : Upper (D 7) (R 7) [36,96,264,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24683 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24684 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 82, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 268 138 81 160 83 147 275), lower := (rows 37 98 268 138 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 301 168 81 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 301 170 17 160 0 160 256) }] }

theorem u24684 : Upper (D 7) (R 7) [36,96,264,130,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24685 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 98, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 268 138 145 33 82 210 338), lower := (rows 37 98 268 138 145 33 64 128 256), losses := [] }

theorem u24685 : Upper (D 7) (R 7) [36,96,264,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24686 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 37 98 268 138 145 34 81 209 337), lower := (rows 37 98 268 138 145 34 64 128 256), losses := [] }

theorem u24686 : Upper (D 7) (R 7) [36,96,264,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24687 : Route 9 := (fun mask => (mask,id))

def c24687 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24687 : Upper (D 7) (R 7) [36,96,264,130,129,16] 13 := by
  apply FastRouting.sound _ _ [36,96,264,130,129,16] 13 (by decide) (choices 1) [1,2] r24687 c24687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8298
  · exact u8299

def b24688 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 268 138 145 96 83 147 275), lower := (rows 37 98 268 138 145 96 64 128 256), losses := [] }

theorem u24688 : Upper (D 7) (R 7) [36,96,264,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24689 : Route 9 := (fun mask => (mask,id))

def c24689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24689 : Upper (D 7) (R 7) [36,96,264,130,192,1] 13 := by
  apply FastRouting.sound _ _ [36,96,264,130,192,1] 13 (by decide) (choices 1) [1,2,16] r24689 c24689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8300
  · exact u8301
  · exact u8302

def b24690 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 42, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 37 98 268 138 208 34 81 145 273), lower := (rows 37 98 268 138 208 34 64 128 256), losses := [] }

theorem u24690 : Upper (D 7) (R 7) [36,96,264,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24691 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 268 138 208 48 67 131 259), lower := (rows 37 98 268 138 208 48 64 128 256), losses := [] }

theorem u24691 : Upper (D 7) (R 7) [36,96,264,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24691 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24692 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 268 152 19 33 194 194 450), lower := (rows 37 98 268 152 19 33 64 128 256), losses := [] }

theorem u24692 : Upper (D 7) (R 7) [36,96,264,144,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24693 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 268 152 19 34 193 193 449), lower := (rows 37 98 268 152 19 34 64 128 256), losses := [] }

theorem u24693 : Upper (D 7) (R 7) [36,96,264,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24694 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 268 152 19 96 195 131 387), lower := (rows 37 98 268 152 19 96 64 128 256), losses := [] }

theorem u24694 : Upper (D 7) (R 7) [36,96,264,144,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24695 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,7),(2,5),(3,5),(4,7)], upper := (rows 37 98 268 152 19 160 67 195 323), lower := (rows 37 98 268 152 19 160 64 128 256), losses := [] }

theorem u24695 : Upper (D 7) (R 7) [36,96,264,144,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24696 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 268 152 81 33 194 130 386), lower := (rows 37 98 268 152 81 33 64 128 256), losses := [] }

theorem u24696 : Upper (D 7) (R 7) [36,96,264,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24697 : Route 9 := (fun mask => (mask,id))

def c24697 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24697 : Upper (D 7) (R 7) [36,96,264,144,65,2] 13 := by
  apply FastRouting.sound _ _ [36,96,264,144,65,2] 13 (by decide) (choices 1) [1,2,128] r24697 c24697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8303
  · exact u8304
  · exact u8305

def b24698 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 82, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 268 152 81 160 67 131 259), lower := (rows 37 98 268 152 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 301 184 81 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 301 184 17 160 0 160 256) }] }

theorem u24698 : Upper (D 7) (R 7) [36,96,264,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24699 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 268 200 19 33 210 146 402), lower := (rows 37 98 268 200 19 33 64 128 256), losses := [] }

theorem u24699 : Upper (D 7) (R 7) [36,96,264,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24700 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 268 200 19 34 209 145 401), lower := (rows 37 98 268 200 19 34 64 128 256), losses := [] }

theorem u24700 : Upper (D 7) (R 7) [36,96,264,192,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24701 : Route 9 := (fun mask => (mask,id))

def c24701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24701 : Upper (D 7) (R 7) [36,96,264,192,3,16] 13 := by
  apply FastRouting.sound _ _ [36,96,264,192,3,16] 13 (by decide) (choices 1) [1,2,128] r24701 c24701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8306
  · exact u8307
  · exact u8308

def b24702 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,7),(2,5),(3,5),(4,7)], upper := (rows 37 98 268 200 19 160 83 147 275), lower := (rows 37 98 268 200 19 160 64 128 256), losses := [] }

theorem u24702 : Upper (D 7) (R 7) [36,96,264,192,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24703 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 98, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 268 200 145 33 82 146 274), lower := (rows 37 98 268 200 145 33 64 128 256), losses := [] }

theorem u24703 : Upper (D 7) (R 7) [36,96,264,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24704 : Route 9 := (fun mask => (mask,id))

def c24704 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24704 : Upper (D 7) (R 7) [36,96,264,192,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,264,192,129,2] 13 (by decide) (choices 1) [1,2,16] r24704 c24704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8309
  · exact u8310
  · exact u8311

def r24705 : Route 9 := (fun mask => (mask,id))

def c24705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24705 : Upper (D 7) (R 7) [36,96,264,192,129,16] 13 := by
  apply FastRouting.sound _ _ [36,96,264,192,129,16] 13 (by decide) (choices 1) [1,2] r24705 c24705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8312
  · exact u8313

def r24706 : Route 9 := (fun mask => (mask,id))

def c24706 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24706 : Upper (D 7) (R 7) [36,96,264,192,130,1] 13 := by
  apply FastRouting.sound _ _ [36,96,264,192,130,1] 13 (by decide) (choices 1) [1,2,16] r24706 c24706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8314
  · exact u8315
  · exact u8316

def b24707 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 50, targets := 1 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 268 200 146 34 81 145 273), lower := (rows 37 98 268 200 146 34 64 128 256), losses := [{ target := 7, region := (rows 5 74 4 8 16 126 64 0 256), good := (rows 37 98 303 106 50 34 98 0 256) }] }

theorem u24707 : Upper (D 7) (R 7) [36,96,264,192,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24708 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 50, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 268 200 146 48 67 131 259), lower := (rows 37 98 268 200 146 48 64 128 256), losses := [] }

theorem u24708 : Upper (D 7) (R 7) [36,96,264,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24708 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24709 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 324 11 145 34 216 152 408), lower := (rows 37 98 324 11 145 34 64 128 256), losses := [] }

theorem u24709 : Upper (D 7) (R 7) [36,96,320,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24710 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 98 324 11 145 40 210 146 402), lower := (rows 37 98 324 11 145 40 64 128 256), losses := [] }

theorem u24710 : Upper (D 7) (R 7) [36,96,320,3,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24710 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24711 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 452, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 37 98 324 11 145 48 202 138 394), lower := (rows 37 98 324 11 145 48 64 128 256), losses := [] }

theorem u24711 : Upper (D 7) (R 7) [36,96,320,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24711 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24712 : Route 9 := (fun mask => (mask,id))

def c24712 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24712 : Upper (D 7) (R 7) [36,96,320,3,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,320,3,129,128] 13 (by decide) (choices 1) [2,8,16] r24712 c24712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8317
  · exact u8318
  · exact u8319

def b24713 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 324 11 146 33 216 152 408), lower := (rows 37 98 324 11 146 33 64 128 256), losses := [] }

theorem u24713 : Upper (D 7) (R 7) [36,96,320,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24714 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 98 324 11 146 40 209 145 401), lower := (rows 37 98 324 11 146 40 64 128 256), losses := [] }

theorem u24714 : Upper (D 7) (R 7) [36,96,320,3,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24714 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24715 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 37 98 324 11 146 48 201 137 393), lower := (rows 37 98 324 11 146 48 64 128 256), losses := [] }

theorem u24715 : Upper (D 7) (R 7) [36,96,320,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24715 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24716 : Route 9 := (fun mask => (mask,id))

def c24716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24716 : Upper (D 7) (R 7) [36,96,320,3,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,320,3,130,128] 13 (by decide) (choices 1) [1,8,16] r24716 c24716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8320
  · exact u8321
  · exact u8322

def b24717 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 324 11 152 33 210 146 402), lower := (rows 37 98 324 11 152 33 64 128 256), losses := [] }

theorem u24717 : Upper (D 7) (R 7) [36,96,320,3,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24718 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 324 11 152 34 209 145 401), lower := (rows 37 98 324 11 152 34 64 128 256), losses := [] }

theorem u24718 : Upper (D 7) (R 7) [36,96,320,3,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24719 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 144, targets := 64 }], pairs := [(2,5),(4,5),(4,6)], upper := (rows 37 98 324 11 152 48 195 131 387), lower := (rows 37 98 324 11 152 48 64 128 256), losses := [] }

theorem u24719 : Upper (D 7) (R 7) [36,96,320,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24719 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24719
end Delivery.IrregularNine14.P07
