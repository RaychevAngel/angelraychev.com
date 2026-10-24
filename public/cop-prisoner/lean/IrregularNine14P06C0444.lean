import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0139

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26640 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 131 324 74 50 48 69 133 261), lower := (rows 41 131 324 74 50 48 64 128 256), losses := [] }

theorem u26640 : Upper (D 6) (R 6) [40,129,320,66,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26640 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26641 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 74 52 33 86 150 278), lower := (rows 41 131 324 74 52 33 64 128 256), losses := [] }

theorem u26641 : Upper (D 6) (R 6) [40,129,320,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26642 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 324 74 52 34 85 149 277), lower := (rows 41 131 324 74 52 34 64 128 256), losses := [] }

theorem u26642 : Upper (D 6) (R 6) [40,129,320,66,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26643 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 131 324 74 52 36 83 147 275), lower := (rows 41 131 324 74 52 36 64 128 256), losses := [] }

theorem u26643 : Upper (D 6) (R 6) [40,129,320,66,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26644 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 131 324 74 52 48 71 135 263), lower := (rows 41 131 324 74 52 48 64 128 256), losses := [] }

theorem u26644 : Upper (D 6) (R 6) [40,129,320,66,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26644 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26645 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 88 22 33 102 166 294), lower := (rows 41 131 324 88 22 33 64 128 256), losses := [] }

theorem u26645 : Upper (D 6) (R 6) [40,129,320,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26646 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 41 131 324 88 22 34 101 165 293), lower := (rows 41 131 324 88 22 34 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 50 64 128 256), good := (rows 41 163 320 121 50 34 64 128 256) },{ target := 6, region := (rows 9 2 4 8 16 50 0 128 256), good := (rows 41 163 260 57 54 34 0 128 256) }] }

theorem u26646 : Upper (D 6) (R 6) [40,129,320,80,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26647 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 130, targets := 4 },{ cop := 0, region := 130, targets := 64 }], pairs := [(0,1),(1,2),(1,6)], upper := (rows 41 131 324 88 22 36 99 163 291), lower := (rows 41 131 324 88 22 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 129 356 121 52 36 64 128 256) }] }

theorem u26647 : Upper (D 6) (R 6) [40,129,320,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26648 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 131 324 88 52 33 70 134 262), lower := (rows 41 131 324 88 52 33 64 128 256), losses := [] }

theorem u26648 : Upper (D 6) (R 6) [40,129,320,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26649 : Route 9 := (fun mask => (mask,id))

def c26649 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26649 : Upper (D 6) (R 6) [40,129,320,80,36,2] 13 := by
  apply FastRouting.sound _ _ [40,129,320,80,36,2] 13 (by decide) (choices 1) [1,2,4] r26649 c26649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8344
  · exact u8345
  · exact u8346

def b26650 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 131 324 88 52 36 67 131 259), lower := (rows 41 131 324 88 52 36 64 128 256), losses := [] }

theorem u26650 : Upper (D 6) (R 6) [40,129,320,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26651 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 41 134 262 11 21 48 96 224 352), lower := (rows 41 134 262 11 21 48 64 128 256), losses := [] }

theorem u26651 : Upper (D 6) (R 6) [40,132,258,3,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26651 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26652 : Route 9 := (fun mask => (mask,id))

def c26652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26652 : Upper (D 6) (R 6) [40,132,258,3,5,64] 13 := by
  apply FastRouting.sound _ _ [40,132,258,3,5,64] 13 (by decide) (choices 1) [16,32] r26652 c26652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8347
  · exact u8348

def b26653 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 134 262 11 52 33 80 208 336), lower := (rows 41 134 262 11 52 33 64 128 256), losses := [] }

theorem u26653 : Upper (D 6) (R 6) [40,132,258,3,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26654 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 134 262 11 52 48 65 193 321), lower := (rows 41 134 262 11 52 48 64 128 256), losses := [] }

theorem u26654 : Upper (D 6) (R 6) [40,132,258,3,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26654 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26655 : Route 9 := (fun mask => (mask,id))

def c26655 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26655 : Upper (D 6) (R 6) [40,132,258,3,36,64] 13 := by
  apply FastRouting.sound _ _ [40,132,258,3,36,64] 13 (by decide) (choices 1) [1,16] r26655 c26655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8349
  · exact u8350

def b26656 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 41 134 262 11 81 36 112 240 368), lower := (rows 41 134 262 11 81 36 64 128 256), losses := [] }

theorem u26656 : Upper (D 6) (R 6) [40,132,258,3,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26657 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 134 262 11 81 48 100 228 356), lower := (rows 41 134 262 11 81 48 64 128 256), losses := [] }

theorem u26657 : Upper (D 6) (R 6) [40,132,258,3,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26657 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26658 : Route 9 := (fun mask => (mask,id))

def c26658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26658 : Upper (D 6) (R 6) [40,132,258,3,65,64] 13 := by
  apply FastRouting.sound _ _ [40,132,258,3,65,64] 13 (by decide) (choices 1) [4,16,32] r26658 c26658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8351
  · exact u8352
  · exact u8353

def b26659 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 262 11 84 33 112 240 368), lower := (rows 41 134 262 11 84 33 64 128 256), losses := [] }

theorem u26659 : Upper (D 6) (R 6) [40,132,258,3,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26660 : Route 9 := (fun mask => (mask,id))

def c26660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26660 : Upper (D 6) (R 6) [40,132,258,3,68,16] 13 := by
  apply FastRouting.sound _ _ [40,132,258,3,68,16] 13 (by decide) (choices 1) [1,32] r26660 c26660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8354
  · exact u8355

def r26661 : Route 9 := (fun mask => (mask,id))

def c26661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26661 : Upper (D 6) (R 6) [40,132,258,3,68,64] 13 := by
  apply FastRouting.sound _ _ [40,132,258,3,68,64] 13 (by decide) (choices 1) [1,16,32] r26661 c26661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8356
  · exact u8357
  · exact u8358

def b26662 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 262 11 112 33 84 212 340), lower := (rows 41 134 262 11 112 33 64 128 256), losses := [] }

theorem u26662 : Upper (D 6) (R 6) [40,132,258,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26663 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 41 134 262 11 112 36 81 209 337), lower := (rows 41 134 262 11 112 36 64 128 256), losses := [] }

theorem u26663 : Upper (D 6) (R 6) [40,132,258,3,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26664 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 134 262 11 112 48 69 197 325), lower := (rows 41 134 262 11 112 48 64 128 256), losses := [] }

theorem u26664 : Upper (D 6) (R 6) [40,132,258,3,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26664 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26665 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 134 262 11 112 96 85 149 277), lower := (rows 41 134 262 11 112 96 64 128 256), losses := [] }

theorem u26665 : Upper (D 6) (R 6) [40,132,258,3,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26666 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 25 82 33 100 228 356), lower := (rows 41 134 262 25 82 33 64 128 256), losses := [] }

theorem u26666 : Upper (D 6) (R 6) [40,132,258,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26667 : PairBound 9 := { available := 97, camps := [], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 134 262 25 82 36 97 225 353), lower := (rows 41 134 262 25 82 36 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 24 16 38 81 145 273), good := (rows 489 164 292 473 505 36 64 128 256) },{ target := 6, region := (rows 17 2 4 24 16 38 0 128 256), good := (rows 41 166 294 25 59 36 0 128 256) }] }

theorem u26667 : Upper (D 6) (R 6) [40,132,258,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26668 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 25 82 96 101 165 293), lower := (rows 41 134 262 25 82 96 64 128 256), losses := [] }

theorem u26668 : Upper (D 6) (R 6) [40,132,258,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26669 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 262 26 21 33 96 224 352), lower := (rows 41 134 262 26 21 33 64 128 256), losses := [] }

theorem u26669 : Upper (D 6) (R 6) [40,132,258,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26670 : Route 9 := (fun mask => (mask,id))

def c26670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26670 : Upper (D 6) (R 6) [40,132,258,18,5,64] 13 := by
  apply FastRouting.sound _ _ [40,132,258,18,5,64] 13 (by decide) (choices 1) [1,32] r26670 c26670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8359
  · exact u8360

def b26671 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 26 81 33 100 228 356), lower := (rows 41 134 262 26 81 33 64 128 256), losses := [] }

theorem u26671 : Upper (D 6) (R 6) [40,132,258,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26672 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 41 134 262 26 81 36 97 225 353), lower := (rows 41 134 262 26 81 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 25 38 73 137 265), good := (rows 505 164 292 505 465 36 64 128 256) }] }

theorem u26672 : Upper (D 6) (R 6) [40,132,258,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26673 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 41 134 262 26 81 96 101 165 293), lower := (rows 41 134 262 26 81 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 112 64 128 256), good := (rows 41 132 260 57 113 96 96 128 256) }] }

theorem u26673 : Upper (D 6) (R 6) [40,132,258,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26674 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 26 84 33 97 225 353), lower := (rows 41 134 262 26 84 33 64 128 256), losses := [] }

theorem u26674 : Upper (D 6) (R 6) [40,132,258,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26675 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 41 134 262 26 84 96 97 161 289), lower := (rows 41 134 262 26 84 96 64 128 256), losses := [] }

theorem u26675 : Upper (D 6) (R 6) [40,132,258,18,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26676 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 26 112 33 69 197 325), lower := (rows 41 134 262 26 112 33 64 128 256), losses := [] }

theorem u26676 : Upper (D 6) (R 6) [40,132,258,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26677 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(4,1),(4,2)], upper := (rows 41 134 262 26 112 36 65 193 321), lower := (rows 41 134 262 26 112 36 64 128 256), losses := [] }

theorem u26677 : Upper (D 6) (R 6) [40,132,258,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26678 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 134 262 26 112 96 69 133 261), lower := (rows 41 134 262 26 112 96 64 128 256), losses := [] }

theorem u26678 : Upper (D 6) (R 6) [40,132,258,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26679 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 41 134 262 73 19 36 112 240 368), lower := (rows 41 134 262 73 19 36 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 24 16 38 80 144 272), good := (rows 41 164 292 73 505 36 64 128 256) }] }

theorem u26679 : Upper (D 6) (R 6) [40,132,258,65,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26680 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 134 262 73 19 48 100 228 356), lower := (rows 41 134 262 73 19 48 64 128 256), losses := [] }

theorem u26680 : Upper (D 6) (R 6) [40,132,258,65,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26680 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26681 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 73 19 96 116 180 308), lower := (rows 41 134 262 73 19 96 64 128 256), losses := [] }

theorem u26681 : Upper (D 6) (R 6) [40,132,258,65,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26682 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 134 262 73 50 33 84 212 340), lower := (rows 41 134 262 73 50 33 64 128 256), losses := [] }

theorem u26682 : Upper (D 6) (R 6) [40,132,258,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26683 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 73 50 36 81 209 337), lower := (rows 41 134 262 73 50 36 64 128 256), losses := [] }

theorem u26683 : Upper (D 6) (R 6) [40,132,258,65,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26684 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 134 262 73 50 48 69 197 325), lower := (rows 41 134 262 73 50 48 64 128 256), losses := [] }

theorem u26684 : Upper (D 6) (R 6) [40,132,258,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26684 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26685 : PairBound 9 := { available := 21, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 73 50 96 85 149 277), lower := (rows 41 134 262 73 50 96 64 128 256), losses := [] }

theorem u26685 : Upper (D 6) (R 6) [40,132,258,65,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26686 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 73 82 33 116 180 308), lower := (rows 41 134 262 73 82 33 64 128 256), losses := [] }

theorem u26686 : Upper (D 6) (R 6) [40,132,258,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26687 : Route 9 := (fun mask => (mask,id))

def c26687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26687 : Upper (D 6) (R 6) [40,132,258,65,66,4] 13 := by
  apply FastRouting.sound _ _ [40,132,258,65,66,4] 13 (by decide) (choices 1) [1,16,32] r26687 c26687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8361
  · exact u8362
  · exact u8363

def b26688 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 134 262 73 82 48 101 165 293), lower := (rows 41 134 262 73 82 48 64 128 256), losses := [] }

theorem u26688 : Upper (D 6) (R 6) [40,132,258,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26688 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26689 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 74 21 33 112 240 368), lower := (rows 41 134 262 74 21 33 64 128 256), losses := [] }

theorem u26689 : Upper (D 6) (R 6) [40,132,258,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26690 : Route 9 := (fun mask => (mask,id))

def c26690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26690 : Upper (D 6) (R 6) [40,132,258,66,5,16] 13 := by
  apply FastRouting.sound _ _ [40,132,258,66,5,16] 13 (by decide) (choices 1) [1,32] r26690 c26690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8364
  · exact u8365

def b26691 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 262 74 21 96 113 177 305), lower := (rows 41 134 262 74 21 96 64 128 256), losses := [] }

theorem u26691 : Upper (D 6) (R 6) [40,132,258,66,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26692 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 74 52 33 81 209 337), lower := (rows 41 134 262 74 52 33 64 128 256), losses := [] }

theorem u26692 : Upper (D 6) (R 6) [40,132,258,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26693 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 134 262 74 52 48 65 193 321), lower := (rows 41 134 262 74 52 48 64 128 256), losses := [] }

theorem u26693 : Upper (D 6) (R 6) [40,132,258,66,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26693 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26694 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 262 74 52 96 81 145 273), lower := (rows 41 134 262 74 52 96 64 128 256), losses := [] }

theorem u26694 : Upper (D 6) (R 6) [40,132,258,66,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26695 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 134 262 74 81 33 116 180 308), lower := (rows 41 134 262 74 81 33 64 128 256), losses := [] }

theorem u26695 : Upper (D 6) (R 6) [40,132,258,66,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26696 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(4,1),(4,2)], upper := (rows 41 134 262 74 81 36 113 177 305), lower := (rows 41 134 262 74 81 36 64 128 256), losses := [] }

theorem u26696 : Upper (D 6) (R 6) [40,132,258,66,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26697 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 134 262 74 81 48 101 165 293), lower := (rows 41 134 262 74 81 48 64 128 256), losses := [] }

theorem u26697 : Upper (D 6) (R 6) [40,132,258,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26697 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26698 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 74 84 33 113 177 305), lower := (rows 41 134 262 74 84 33 64 128 256), losses := [] }

theorem u26698 : Upper (D 6) (R 6) [40,132,258,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26699 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 41 134 262 74 84 48 97 161 289), lower := (rows 41 134 262 74 84 48 64 128 256), losses := [] }

theorem u26699 : Upper (D 6) (R 6) [40,132,258,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26699 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26699
end Delivery.IrregularNine14.P06
