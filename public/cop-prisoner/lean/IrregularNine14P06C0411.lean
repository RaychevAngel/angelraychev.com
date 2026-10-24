import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0126
import IrregularNine14P06C0127

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24660 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 13 273 34 116 180 308), lower := (rows 35 194 76 13 273 34 64 128 256), losses := [] }

theorem u24660 : Upper (D 6) (R 6) [34,192,72,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24661 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 76 13 273 36 114 178 306), lower := (rows 35 194 76 13 273 36 64 128 256), losses := [] }

theorem u24661 : Upper (D 6) (R 6) [34,192,72,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24662 : Route 9 := (fun mask => (mask,id))

def c24662 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24662 : Upper (D 6) (R 6) [34,192,72,5,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,5,257,16] 13 (by decide) (choices 1) [2,4,32] r24662 c24662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7591
  · exact u7592
  · exact u7593

def r24663 : Route 9 := (fun mask => (mask,id))

def c24663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24663 : Upper (D 6) (R 6) [34,192,72,5,258,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,5,258,1] 13 (by decide) (choices 1) [4,16,32] r24663 c24663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7594
  · exact u7595
  · exact u7596

def b24664 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 76 13 274 36 113 177 305), lower := (rows 35 194 76 13 274 36 64 128 256), losses := [] }

theorem u24664 : Upper (D 6) (R 6) [34,192,72,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24665 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 76 13 274 48 101 165 293), lower := (rows 35 194 76 13 274 48 64 128 256), losses := [] }

theorem u24665 : Upper (D 6) (R 6) [34,192,72,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24665 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24666 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 76 13 276 33 114 178 306), lower := (rows 35 194 76 13 276 33 64 128 256), losses := [] }

theorem u24666 : Upper (D 6) (R 6) [34,192,72,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24667 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 13 276 34 113 177 305), lower := (rows 35 194 76 13 276 34 64 128 256), losses := [] }

theorem u24667 : Upper (D 6) (R 6) [34,192,72,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24668 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 194 76 13 276 48 99 163 291), lower := (rows 35 194 76 13 276 48 64 128 256), losses := [] }

theorem u24668 : Upper (D 6) (R 6) [34,192,72,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24668 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24669 : Route 9 := (fun mask => (mask,id))

def c24669 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24669 : Upper (D 6) (R 6) [34,192,72,5,288,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,5,288,1] 13 (by decide) (choices 1) [2,4,16] r24669 c24669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7597
  · exact u7598
  · exact u7599

def b24670 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 13 304 34 85 149 277), lower := (rows 35 194 76 13 304 34 64 128 256), losses := [] }

theorem u24670 : Upper (D 6) (R 6) [34,192,72,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24671 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 76 13 304 36 83 147 275), lower := (rows 35 194 76 13 304 36 64 128 256), losses := [] }

theorem u24671 : Upper (D 6) (R 6) [34,192,72,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24672 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 194 76 13 304 48 71 135 263), lower := (rows 35 194 76 13 304 48 64 128 256), losses := [] }

theorem u24672 : Upper (D 6) (R 6) [34,192,72,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24672 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24673 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 25 52 33 326 390 262), lower := (rows 35 194 76 25 52 33 64 128 256), losses := [] }

theorem u24673 : Upper (D 6) (R 6) [34,192,72,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24674 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 25 52 34 325 389 261), lower := (rows 35 194 76 25 52 34 64 128 256), losses := [] }

theorem u24674 : Upper (D 6) (R 6) [34,192,72,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24675 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 76 25 52 36 323 387 259), lower := (rows 35 194 76 25 52 36 64 128 256), losses := [] }

theorem u24675 : Upper (D 6) (R 6) [34,192,72,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24676 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 76 25 52 288 71 135 263), lower := (rows 35 194 76 25 52 288 64 128 256), losses := [] }

theorem u24676 : Upper (D 6) (R 6) [34,192,72,17,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24676 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24677 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 194 76 25 274 33 100 164 292), lower := (rows 35 194 76 25 274 33 64 128 256), losses := [] }

theorem u24677 : Upper (D 6) (R 6) [34,192,72,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24678 : Route 9 := (fun mask => (mask,id))

def c24678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24678 : Upper (D 6) (R 6) [34,192,72,17,258,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,17,258,4] 13 (by decide) (choices 1) [1,4,32] r24678 c24678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7600
  · exact u7601
  · exact u7602

def r24679 : Route 9 := (fun mask => (mask,id))

def c24679 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24679 : Upper (D 6) (R 6) [34,192,72,17,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,17,260,1] 13 (by decide) (choices 1) [2,4,32] r24679 c24679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7603
  · exact u7604
  · exact u7605

def b24680 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 25 276 34 101 165 293), lower := (rows 35 194 76 25 276 34 64 128 256), losses := [] }

theorem u24680 : Upper (D 6) (R 6) [34,192,72,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24681 : Route 9 := (fun mask => (mask,id))

def c24681 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24681 : Upper (D 6) (R 6) [34,192,72,17,260,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,17,260,4] 13 (by decide) (choices 1) [1,2,32] r24681 c24681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7606
  · exact u7607
  · exact u7608

def b24682 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 25 304 33 70 134 262), lower := (rows 35 194 76 25 304 33 64 128 256), losses := [] }

theorem u24682 : Upper (D 6) (R 6) [34,192,72,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24683 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 25 304 34 69 133 261), lower := (rows 35 194 76 25 304 34 64 128 256), losses := [] }

theorem u24683 : Upper (D 6) (R 6) [34,192,72,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24684 : Route 9 := (fun mask => (mask,id))

def c24684 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24684 : Upper (D 6) (R 6) [34,192,72,17,288,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,17,288,4] 13 (by decide) (choices 1) [1,2,4] r24684 c24684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7609
  · exact u7610
  · exact u7611

def b24685 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 76 26 52 33 325 389 261), lower := (rows 35 194 76 26 52 33 64 128 256), losses := [{ target := 6, region := (rows 11 2 4 8 20 47 0 132 260), good := (rows 35 163 445 59 436 33 0 128 256) }] }

theorem u24685 : Upper (D 6) (R 6) [34,192,72,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24686 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 60, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 76 26 52 36 321 385 257), lower := (rows 35 194 76 26 52 36 64 128 256), losses := [] }

theorem u24686 : Upper (D 6) (R 6) [34,192,72,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24687 : PairBound 9 := { available := 5, camps := [], pairs := [(0,6),(4,6)], upper := (rows 35 194 76 26 52 288 69 133 261), lower := (rows 35 194 76 26 52 288 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 20 308 0 132 260), good := (rows 35 130 445 59 436 288 0 128 288) }] }

theorem u24687 : Upper (D 6) (R 6) [34,192,72,18,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24687 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24688 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 194 76 26 273 33 100 164 292), lower := (rows 35 194 76 26 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 72 136 264), good := (rows 33 192 460 508 305 33 64 128 256) }] }

theorem u24688 : Upper (D 6) (R 6) [34,192,72,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24689 : Route 9 := (fun mask => (mask,id))

def c24689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24689 : Upper (D 6) (R 6) [34,192,72,18,257,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,18,257,4] 13 (by decide) (choices 1) [1,4,32] r24689 c24689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7612
  · exact u7613
  · exact u7614

def b24690 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 76 26 276 33 101 165 293), lower := (rows 35 194 76 26 276 33 64 128 256), losses := [{ target := 6, region := (rows 11 2 4 8 20 47 0 132 260), good := (rows 35 163 445 59 436 33 0 128 256) }] }

theorem u24690 : Upper (D 6) (R 6) [34,192,72,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24691 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 76 26 276 36 97 161 289), lower := (rows 35 194 76 26 276 36 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 9 52 52 0 141 269), good := (rows 443 130 445 443 436 436 0 128 256) }] }

theorem u24691 : Upper (D 6) (R 6) [34,192,72,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24692 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 76 26 304 33 69 133 261), lower := (rows 35 194 76 26 304 33 64 128 256), losses := [{ target := 6, region := (rows 11 2 4 8 20 47 0 132 260), good := (rows 35 163 445 59 304 33 0 128 256) }] }

theorem u24692 : Upper (D 6) (R 6) [34,192,72,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24693 : Route 9 := (fun mask => (mask,id))

def c24693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24693 : Upper (D 6) (R 6) [34,192,72,18,288,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,18,288,4] 13 (by decide) (choices 1) [1,4] r24693 c24693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7615
  · exact u7616

def r24694 : Route 9 := (fun mask => (mask,id))

def c24694 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24694 : Upper (D 6) (R 6) [34,192,72,20,257,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,20,257,1] 13 (by decide) (choices 1) [2,4,32] r24694 c24694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7617
  · exact u7618
  · exact u7619

def b24695 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 28 273 34 101 165 293), lower := (rows 35 194 76 28 273 34 64 128 256), losses := [] }

theorem u24695 : Upper (D 6) (R 6) [34,192,72,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24696 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 76 28 273 36 99 163 291), lower := (rows 35 194 76 28 273 36 64 128 256), losses := [] }

theorem u24696 : Upper (D 6) (R 6) [34,192,72,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24697 : Route 9 := (fun mask => (mask,id))

def c24697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24697 : Upper (D 6) (R 6) [34,192,72,20,258,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,20,258,1] 13 (by decide) (choices 1) [1,4,32] r24697 c24697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7620
  · exact u7621
  · exact u7622

def b24698 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 76 28 274 36 97 161 289), lower := (rows 35 194 76 28 274 36 64 128 256), losses := [] }

theorem u24698 : Upper (D 6) (R 6) [34,192,72,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24699 : Route 9 := (fun mask => (mask,id))

def c24699 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24699 : Upper (D 6) (R 6) [34,192,72,20,288,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,20,288,1] 13 (by decide) (choices 1) [1,2,4] r24699 c24699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7623
  · exact u7624
  · exact u7625

def b24700 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 28 304 34 69 133 261), lower := (rows 35 194 76 28 304 34 64 128 256), losses := [] }

theorem u24700 : Upper (D 6) (R 6) [34,192,72,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24701 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 76 28 304 36 67 131 259), lower := (rows 35 194 76 28 304 36 64 128 256), losses := [] }

theorem u24701 : Upper (D 6) (R 6) [34,192,72,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24702 : Route 9 := (fun mask => (mask,id))

def c24702 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24702 : Upper (D 6) (R 6) [34,192,72,36,257,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,36,257,1] 13 (by decide) (choices 1) [2,4,16] r24702 c24702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7626
  · exact u7627
  · exact u7628

def b24703 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 44 273 34 85 149 277), lower := (rows 35 194 76 44 273 34 64 128 256), losses := [] }

theorem u24703 : Upper (D 6) (R 6) [34,192,72,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24704 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 76 44 273 36 83 147 275), lower := (rows 35 194 76 44 273 36 64 128 256), losses := [] }

theorem u24704 : Upper (D 6) (R 6) [34,192,72,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24705 : Route 9 := (fun mask => (mask,id))

def c24705 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24705 : Upper (D 6) (R 6) [34,192,72,36,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,36,257,16] 13 (by decide) (choices 1) [1,2,4] r24705 c24705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7629
  · exact u7630
  · exact u7631

def r24706 : Route 9 := (fun mask => (mask,id))

def c24706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24706 : Upper (D 6) (R 6) [34,192,72,36,258,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,36,258,1] 13 (by decide) (choices 1) [1,4,16] r24706 c24706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7632
  · exact u7633
  · exact u7634

def b24707 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 76 44 274 36 81 145 273), lower := (rows 35 194 76 44 274 36 64 128 256), losses := [] }

theorem u24707 : Upper (D 6) (R 6) [34,192,72,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24708 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 76 44 274 48 69 133 261), lower := (rows 35 194 76 44 274 48 64 128 256), losses := [] }

theorem u24708 : Upper (D 6) (R 6) [34,192,72,36,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24708 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24709 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 76 44 276 33 83 147 275), lower := (rows 35 194 76 44 276 33 64 128 256), losses := [] }

theorem u24709 : Upper (D 6) (R 6) [34,192,72,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24710 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 44 276 34 81 145 273), lower := (rows 35 194 76 44 276 34 64 128 256), losses := [] }

theorem u24710 : Upper (D 6) (R 6) [34,192,72,36,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24711 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 194 76 44 276 48 67 131 259), lower := (rows 35 194 76 44 276 48 64 128 256), losses := [] }

theorem u24711 : Upper (D 6) (R 6) [34,192,72,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24711 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24712 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 56 21 33 326 390 262), lower := (rows 35 194 76 56 21 33 64 128 256), losses := [] }

theorem u24712 : Upper (D 6) (R 6) [34,192,72,48,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24713 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 56 21 34 325 389 261), lower := (rows 35 194 76 56 21 34 64 128 256), losses := [] }

theorem u24713 : Upper (D 6) (R 6) [34,192,72,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24714 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 194 76 56 21 36 323 387 259), lower := (rows 35 194 76 56 21 36 64 128 256), losses := [] }

theorem u24714 : Upper (D 6) (R 6) [34,192,72,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24715 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 76 56 21 288 71 135 263), lower := (rows 35 194 76 56 21 288 64 128 256), losses := [{ target := 5, region := (rows 1 26 12 8 16 0 80 144 272), good := (rows 3 194 78 478 471 256 64 128 256) }] }

theorem u24715 : Upper (D 6) (R 6) [34,192,72,48,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24715 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24716 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 194 76 56 22 33 325 389 261), lower := (rows 35 194 76 56 22 33 64 128 256), losses := [] }

theorem u24716 : Upper (D 6) (R 6) [34,192,72,48,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24717 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 60, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 76 56 22 36 321 385 257), lower := (rows 35 194 76 56 22 36 64 128 256), losses := [] }

theorem u24717 : Upper (D 6) (R 6) [34,192,72,48,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24718 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 194 76 56 22 288 69 133 261), lower := (rows 35 194 76 56 22 288 64 128 256), losses := [] }

theorem u24718 : Upper (D 6) (R 6) [34,192,72,48,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24718 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24719 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 56 273 33 70 134 262), lower := (rows 35 194 76 56 273 33 64 128 256), losses := [] }

theorem u24719 : Upper (D 6) (R 6) [34,192,72,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24719
end Delivery.IrregularNine14.P06
