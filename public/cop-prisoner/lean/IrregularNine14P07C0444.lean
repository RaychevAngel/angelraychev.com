import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0160

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26640 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 266 84 168 19 33 194 194 450), lower := (rows 37 266 84 168 19 33 64 128 256), losses := [] }

theorem u26640 : Upper (D 7) (R 7) [36,264,80,160,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26641 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 196, targets := 34 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(2,1),(2,5),(3,1)], upper := (rows 37 266 84 168 19 34 193 193 449), lower := (rows 37 266 84 168 19 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 50 0 128 256), good := (rows 37 298 53 168 51 34 0 128 256) }] }

theorem u26641 : Upper (D 7) (R 7) [36,264,80,160,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26642 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 168 19 96 195 131 387), lower := (rows 37 266 84 168 19 96 64 128 256), losses := [] }

theorem u26642 : Upper (D 7) (R 7) [36,264,80,160,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26643 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 266 84 168 19 160 67 195 323), lower := (rows 37 266 84 168 19 160 64 128 256), losses := [] }

theorem u26643 : Upper (D 7) (R 7) [36,264,80,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26644 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 266 84 168 145 33 66 194 322), lower := (rows 37 266 84 168 145 33 64 128 256), losses := [] }

theorem u26644 : Upper (D 7) (R 7) [36,264,80,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26645 : Route 9 := (fun mask => (mask,id))

def c26645 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26645 : Upper (D 7) (R 7) [36,264,80,160,129,2] 13 := by
  apply FastRouting.sound _ _ [36,264,80,160,129,2] 13 (by decide) (choices 1) [1,2] r26645 c26645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9604
  · exact u9605

def b26646 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 168 145 96 67 131 259), lower := (rows 37 266 84 168 145 96 64 128 256), losses := [] }

theorem u26646 : Upper (D 7) (R 7) [36,264,80,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26647 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 266 84 168 146 33 67 195 323), lower := (rows 37 266 84 168 146 33 64 128 256), losses := [] }

theorem u26647 : Upper (D 7) (R 7) [36,264,80,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26648 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 65 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(3,0),(3,6)], upper := (rows 37 266 84 168 146 34 65 193 321), lower := (rows 37 266 84 168 146 34 64 128 256), losses := [] }

theorem u26648 : Upper (D 7) (R 7) [36,264,80,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26649 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 84 168 146 96 67 131 259), lower := (rows 37 266 84 168 146 96 64 128 256), losses := [] }

theorem u26649 : Upper (D 7) (R 7) [36,264,80,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26650 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 266 84 200 19 33 226 162 418), lower := (rows 37 266 84 200 19 33 64 128 256), losses := [] }

theorem u26650 : Upper (D 7) (R 7) [36,264,80,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26651 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(0,7),(2,1),(3,1)], upper := (rows 37 266 84 200 19 34 225 161 417), lower := (rows 37 266 84 200 19 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 32 65 129 257), good := (rows 493 264 92 200 477 32 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 50 0 149 277), good := (rows 421 298 437 136 435 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 50 64 0 256), good := (rows 37 298 117 72 51 34 64 0 256) }] }

theorem u26651 : Upper (D 7) (R 7) [36,264,80,192,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26652 : Route 9 := (fun mask => (mask,id))

def c26652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26652 : Upper (D 7) (R 7) [36,264,80,192,3,128] 13 := by
  apply FastRouting.sound _ _ [36,264,80,192,3,128] 13 (by decide) (choices 1) [1,2,32] r26652 c26652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9606
  · exact u9607
  · exact u9608

def b26653 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 266 84 200 50 33 195 131 387), lower := (rows 37 266 84 200 50 33 64 128 256), losses := [] }

theorem u26653 : Upper (D 7) (R 7) [36,264,80,192,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26654 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 266 84 200 50 34 193 129 385), lower := (rows 37 266 84 200 50 34 64 128 256), losses := [] }

theorem u26654 : Upper (D 7) (R 7) [36,264,80,192,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26655 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 4, region := 69, targets := 128 }], pairs := [(0,7),(1,5),(2,7),(3,5)], upper := (rows 37 266 84 200 50 160 67 131 259), lower := (rows 37 266 84 200 50 160 64 128 256), losses := [] }

theorem u26655 : Upper (D 7) (R 7) [36,264,80,192,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26656 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 266 84 200 145 33 98 162 290), lower := (rows 37 266 84 200 145 33 64 128 256), losses := [] }

theorem u26656 : Upper (D 7) (R 7) [36,264,80,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26657 : Route 9 := (fun mask => (mask,id))

def c26657 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26657 : Upper (D 7) (R 7) [36,264,80,192,129,2] 13 := by
  apply FastRouting.sound _ _ [36,264,80,192,129,2] 13 (by decide) (choices 1) [1,2,32] r26657 c26657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9609
  · exact u9610
  · exact u9611

def b26658 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 266 84 200 146 33 99 163 291), lower := (rows 37 266 84 200 146 33 64 128 256), losses := [] }

theorem u26658 : Upper (D 7) (R 7) [36,264,80,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26659 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(0,7),(2,7),(3,1)], upper := (rows 37 266 84 200 146 34 97 161 289), lower := (rows 37 266 84 200 146 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 50 0 133 261), good := (rows 421 298 437 136 178 34 0 128 256) }] }

theorem u26659 : Upper (D 7) (R 7) [36,264,80,192,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26660 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 266 84 200 176 33 67 131 259), lower := (rows 37 266 84 200 176 33 64 128 256), losses := [] }

theorem u26660 : Upper (D 7) (R 7) [36,264,80,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26661 : Route 9 := (fun mask => (mask,id))

def c26661 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26661 : Upper (D 7) (R 7) [36,264,80,192,160,2] 13 := by
  apply FastRouting.sound _ _ [36,264,80,192,160,2] 13 (by decide) (choices 1) [1,2] r26661 c26661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9612
  · exact u9613

def b26662 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 48, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 266 196 11 50 33 208 208 464), lower := (rows 37 266 196 11 50 33 64 128 256), losses := [] }

theorem u26662 : Upper (D 7) (R 7) [36,264,192,3,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26663 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 196 11 50 48 193 193 449), lower := (rows 37 266 196 11 50 48 64 128 256), losses := [] }

theorem u26663 : Upper (D 7) (R 7) [36,264,192,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26663 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26664 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 196 11 50 96 209 145 401), lower := (rows 37 266 196 11 50 96 64 128 256), losses := [] }

theorem u26664 : Upper (D 7) (R 7) [36,264,192,3,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26665 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(4,1)], upper := (rows 37 266 196 11 81 34 240 176 432), lower := (rows 37 266 196 11 81 34 64 128 256), losses := [] }

theorem u26665 : Upper (D 7) (R 7) [36,264,192,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26666 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 266 196 11 81 48 226 162 418), lower := (rows 37 266 196 11 81 48 64 128 256), losses := [] }

theorem u26666 : Upper (D 7) (R 7) [36,264,192,3,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26666 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26667 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 11 81 160 114 178 306), lower := (rows 37 266 196 11 81 160 64 128 256), losses := [] }

theorem u26667 : Upper (D 7) (R 7) [36,264,192,3,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26668 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 196 11 82 33 240 176 432), lower := (rows 37 266 196 11 82 33 64 128 256), losses := [] }

theorem u26668 : Upper (D 7) (R 7) [36,264,192,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26669 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(1,6),(3,6)], upper := (rows 37 266 196 11 82 48 225 161 417), lower := (rows 37 266 196 11 82 48 64 128 256), losses := [] }

theorem u26669 : Upper (D 7) (R 7) [36,264,192,3,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26669 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26670 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 11 82 160 113 177 305), lower := (rows 37 266 196 11 82 160 64 128 256), losses := [] }

theorem u26670 : Upper (D 7) (R 7) [36,264,192,3,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26671 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 266 196 11 112 33 210 146 402), lower := (rows 37 266 196 11 112 33 64 128 256), losses := [] }

theorem u26671 : Upper (D 7) (R 7) [36,264,192,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26672 : Route 9 := (fun mask => (mask,id))

def c26672 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26672 : Upper (D 7) (R 7) [36,264,192,3,96,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,3,96,2] 13 (by decide) (choices 1) [1,16,128] r26672 c26672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9614
  · exact u9615
  · exact u9616

def b26673 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 266 196 11 112 48 195 131 387), lower := (rows 37 266 196 11 112 48 64 128 256), losses := [] }

theorem u26673 : Upper (D 7) (R 7) [36,264,192,3,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26673 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26674 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 11 112 160 83 147 275), lower := (rows 37 266 196 11 112 160 64 128 256), losses := [] }

theorem u26674 : Upper (D 7) (R 7) [36,264,192,3,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26675 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 266 196 25 50 33 194 194 450), lower := (rows 37 266 196 25 50 33 64 128 256), losses := [] }

theorem u26675 : Upper (D 7) (R 7) [36,264,192,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26676 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 266 196 25 50 34 193 193 449), lower := (rows 37 266 196 25 50 34 64 128 256), losses := [] }

theorem u26676 : Upper (D 7) (R 7) [36,264,192,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26677 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 196 25 50 96 195 131 387), lower := (rows 37 266 196 25 50 96 64 128 256), losses := [] }

theorem u26677 : Upper (D 7) (R 7) [36,264,192,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26678 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 266 196 25 82 33 226 162 418), lower := (rows 37 266 196 25 82 33 64 128 256), losses := [] }

theorem u26678 : Upper (D 7) (R 7) [36,264,192,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26679 : Route 9 := (fun mask => (mask,id))

def c26679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26679 : Upper (D 7) (R 7) [36,264,192,17,66,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,17,66,2] 13 (by decide) (choices 1) [1,32,128] r26679 c26679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9617
  · exact u9618
  · exact u9619

def b26680 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 25 82 160 99 163 291), lower := (rows 37 266 196 25 82 160 64 128 256), losses := [] }

theorem u26680 : Upper (D 7) (R 7) [36,264,192,17,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26681 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 57, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 196 25 112 33 194 130 386), lower := (rows 37 266 196 25 112 33 64 128 256), losses := [] }

theorem u26681 : Upper (D 7) (R 7) [36,264,192,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26682 : Route 9 := (fun mask => (mask,id))

def c26682 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26682 : Upper (D 7) (R 7) [36,264,192,17,96,2] 13 := by
  apply FastRouting.sound _ _ [36,264,192,17,96,2] 13 (by decide) (choices 1) [1,2,128] r26682 c26682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9620
  · exact u9621
  · exact u9622

def b26683 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 25 112 160 67 131 259), lower := (rows 37 266 196 25 112 160 64 128 256), losses := [] }

theorem u26683 : Upper (D 7) (R 7) [36,264,192,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26684 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 266 196 26 81 33 226 162 418), lower := (rows 37 266 196 26 81 33 64 128 256), losses := [] }

theorem u26684 : Upper (D 7) (R 7) [36,264,192,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26685 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(4,1)], upper := (rows 37 266 196 26 81 34 225 161 417), lower := (rows 37 266 196 26 81 34 64 128 256), losses := [] }

theorem u26685 : Upper (D 7) (R 7) [36,264,192,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26686 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 26 81 160 99 163 291), lower := (rows 37 266 196 26 81 160 64 128 256), losses := [] }

theorem u26686 : Upper (D 7) (R 7) [36,264,192,18,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26687 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 266 196 26 112 33 195 131 387), lower := (rows 37 266 196 26 112 33 64 128 256), losses := [] }

theorem u26687 : Upper (D 7) (R 7) [36,264,192,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26688 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,1),(2,1),(2,5),(4,1)], upper := (rows 37 266 196 26 112 34 193 129 385), lower := (rows 37 266 196 26 112 34 64 128 256), losses := [] }

theorem u26688 : Upper (D 7) (R 7) [36,264,192,18,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26689 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 26 112 160 67 131 259), lower := (rows 37 266 196 26 112 160 64 128 256), losses := [] }

theorem u26689 : Upper (D 7) (R 7) [36,264,192,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26690 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 196, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 266 196 42 19 33 208 208 464), lower := (rows 37 266 196 42 19 33 64 128 256), losses := [] }

theorem u26690 : Upper (D 7) (R 7) [36,264,192,34,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26691 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 266 196 42 19 48 193 193 449), lower := (rows 37 266 196 42 19 48 64 128 256), losses := [] }

theorem u26691 : Upper (D 7) (R 7) [36,264,192,34,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26691 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26692 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 196 42 19 96 209 145 401), lower := (rows 37 266 196 42 19 96 64 128 256), losses := [] }

theorem u26692 : Upper (D 7) (R 7) [36,264,192,34,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26693 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 266 196 42 81 33 210 146 402), lower := (rows 37 266 196 42 81 33 64 128 256), losses := [] }

theorem u26693 : Upper (D 7) (R 7) [36,264,192,34,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26694 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 42, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 266 196 42 81 34 209 145 401), lower := (rows 37 266 196 42 81 34 64 128 256), losses := [] }

theorem u26694 : Upper (D 7) (R 7) [36,264,192,34,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26695 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 266 196 42 81 48 195 131 387), lower := (rows 37 266 196 42 81 48 64 128 256), losses := [] }

theorem u26695 : Upper (D 7) (R 7) [36,264,192,34,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26695 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26696 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 42 81 160 83 147 275), lower := (rows 37 266 196 42 81 160 64 128 256), losses := [] }

theorem u26696 : Upper (D 7) (R 7) [36,264,192,34,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26697 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 196 42 82 33 209 145 401), lower := (rows 37 266 196 42 82 33 64 128 256), losses := [] }

theorem u26697 : Upper (D 7) (R 7) [36,264,192,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26698 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 266 196 42 82 48 193 129 385), lower := (rows 37 266 196 42 82 48 64 128 256), losses := [] }

theorem u26698 : Upper (D 7) (R 7) [36,264,192,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26698 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26699 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 42 82 160 81 145 273), lower := (rows 37 266 196 42 82 160 64 128 256), losses := [] }

theorem u26699 : Upper (D 7) (R 7) [36,264,192,34,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26699
end Delivery.IrregularNine14.P07
