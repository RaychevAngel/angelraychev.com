import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0127

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24720 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 56 273 34 69 133 261), lower := (rows 35 194 76 56 273 34 64 128 256), losses := [] }

theorem u24720 : Upper (D 6) (R 6) [34,192,72,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24721 : Route 9 := (fun mask => (mask,id))

def c24721 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24721 : Upper (D 6) (R 6) [34,192,72,48,257,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,48,257,4] 13 (by decide) (choices 1) [1,2,4] r24721 c24721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7635
  · exact u7636
  · exact u7637

def b24722 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 194 76 56 274 33 69 133 261), lower := (rows 35 194 76 56 274 33 64 128 256), losses := [] }

theorem u24722 : Upper (D 6) (R 6) [34,192,72,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24723 : Route 9 := (fun mask => (mask,id))

def c24723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24723 : Upper (D 6) (R 6) [34,192,72,48,258,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,48,258,4] 13 (by decide) (choices 1) [1,4] r24723 c24723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7638
  · exact u7639

def r24724 : Route 9 := (fun mask => (mask,id))

def c24724 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24724 : Upper (D 6) (R 6) [34,192,72,48,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,48,260,1] 13 (by decide) (choices 1) [1,2,4] r24724 c24724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7640
  · exact u7641
  · exact u7642

def b24725 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 56 276 34 69 133 261), lower := (rows 35 194 76 56 276 34 64 128 256), losses := [] }

theorem u24725 : Upper (D 6) (R 6) [34,192,72,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24726 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 194 76 56 276 36 67 131 259), lower := (rows 35 194 76 56 276 36 64 128 256), losses := [] }

theorem u24726 : Upper (D 6) (R 6) [34,192,72,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24727 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 265 21 34 116 180 308), lower := (rows 35 194 76 265 21 34 64 128 256), losses := [] }

theorem u24727 : Upper (D 6) (R 6) [34,192,72,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24728 : Route 9 := (fun mask => (mask,id))

def c24728 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24728 : Upper (D 6) (R 6) [34,192,72,257,5,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,5,4] 13 (by decide) (choices 1) [2,16,32] r24728 c24728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7643
  · exact u7644
  · exact u7645

def r24729 : Route 9 := (fun mask => (mask,id))

def c24729 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24729 : Upper (D 6) (R 6) [34,192,72,257,5,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,5,16] 13 (by decide) (choices 1) [2,4,32] r24729 c24729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7646
  · exact u7647
  · exact u7648

def b24730 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 297, targets := 64 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 194 76 265 22 33 116 180 308), lower := (rows 35 194 76 265 22 33 64 128 256), losses := [] }

theorem u24730 : Upper (D 6) (R 6) [34,192,72,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24731 : Route 9 := (fun mask => (mask,id))

def c24731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24731 : Upper (D 6) (R 6) [34,192,72,257,6,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,6,4] 13 (by decide) (choices 1) [1,16,32] r24731 c24731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7649
  · exact u7650
  · exact u7651

def b24732 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 76 265 22 48 101 165 293), lower := (rows 35 194 76 265 22 48 64 128 256), losses := [] }

theorem u24732 : Upper (D 6) (R 6) [34,192,72,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24732 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24733 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 194 76 265 52 33 86 150 278), lower := (rows 35 194 76 265 52 33 64 128 256), losses := [] }

theorem u24733 : Upper (D 6) (R 6) [34,192,72,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24734 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 265 52 34 85 149 277), lower := (rows 35 194 76 265 52 34 64 128 256), losses := [] }

theorem u24734 : Upper (D 6) (R 6) [34,192,72,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24735 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 76 265 52 36 83 147 275), lower := (rows 35 194 76 265 52 36 64 128 256), losses := [] }

theorem u24735 : Upper (D 6) (R 6) [34,192,72,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24736 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 76 265 52 48 71 135 263), lower := (rows 35 194 76 265 52 48 64 128 256), losses := [] }

theorem u24736 : Upper (D 6) (R 6) [34,192,72,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24736 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24737 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 76 266 21 33 116 180 308), lower := (rows 35 194 76 266 21 33 64 128 256), losses := [{ target := 6, region := (rows 11 2 4 8 20 63 0 148 276), good := (rows 35 163 445 299 437 33 0 128 256) }] }

theorem u24737 : Upper (D 6) (R 6) [34,192,72,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24738 : Route 9 := (fun mask => (mask,id))

def c24738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24738 : Upper (D 6) (R 6) [34,192,72,258,5,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,258,5,4] 13 (by decide) (choices 1) [1,16,32] r24738 c24738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7652
  · exact u7653
  · exact u7654

def r24739 : Route 9 := (fun mask => (mask,id))

def c24739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24739 : Upper (D 6) (R 6) [34,192,72,258,5,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,258,5,16] 13 (by decide) (choices 1) [1,4,32] r24739 c24739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7655
  · exact u7656
  · exact u7657

def b24740 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 76 266 52 33 85 149 277), lower := (rows 35 194 76 266 52 33 64 128 256), losses := [{ target := 6, region := (rows 11 2 4 8 20 47 0 132 260), good := (rows 35 163 445 299 436 33 0 128 256) }] }

theorem u24740 : Upper (D 6) (R 6) [34,192,72,258,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24741 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 76 266 52 36 81 145 273), lower := (rows 35 194 76 266 52 36 64 128 256), losses := [] }

theorem u24741 : Upper (D 6) (R 6) [34,192,72,258,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24742 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 76 266 52 48 69 133 261), lower := (rows 35 194 76 266 52 48 64 128 256), losses := [] }

theorem u24742 : Upper (D 6) (R 6) [34,192,72,258,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24742 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24743 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 226, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 76 268 21 33 114 178 306), lower := (rows 35 194 76 268 21 33 64 128 256), losses := [] }

theorem u24743 : Upper (D 6) (R 6) [34,192,72,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24744 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 268 21 34 113 177 305), lower := (rows 35 194 76 268 21 34 64 128 256), losses := [] }

theorem u24744 : Upper (D 6) (R 6) [34,192,72,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24745 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 194 76 268 21 48 99 163 291), lower := (rows 35 194 76 268 21 48 64 128 256), losses := [] }

theorem u24745 : Upper (D 6) (R 6) [34,192,72,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24745 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24746 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 195, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 76 268 52 33 83 147 275), lower := (rows 35 194 76 268 52 33 64 128 256), losses := [] }

theorem u24746 : Upper (D 6) (R 6) [34,192,72,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24747 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 268 52 34 81 145 273), lower := (rows 35 194 76 268 52 34 64 128 256), losses := [] }

theorem u24747 : Upper (D 6) (R 6) [34,192,72,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24748 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 76 268 52 48 67 131 259), lower := (rows 35 194 76 268 52 48 64 128 256), losses := [] }

theorem u24748 : Upper (D 6) (R 6) [34,192,72,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24748 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24749 : Route 9 := (fun mask => (mask,id))

def c24749 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24749 : Upper (D 6) (R 6) [34,192,72,272,5,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,5,1] 13 (by decide) (choices 1) [2,4,32] r24749 c24749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7658
  · exact u7659
  · exact u7660

def b24750 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 280 21 34 101 165 293), lower := (rows 35 194 76 280 21 34 64 128 256), losses := [] }

theorem u24750 : Upper (D 6) (R 6) [34,192,72,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24751 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 194 76 280 21 36 99 163 291), lower := (rows 35 194 76 280 21 36 64 128 256), losses := [{ target := 2, region := (rows 33 51 0 24 16 32 97 161 289), good := (rows 483 194 72 282 475 483 64 128 256) }] }

theorem u24751 : Upper (D 6) (R 6) [34,192,72,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24752 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 297, targets := 64 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 194 76 280 22 33 101 165 293), lower := (rows 35 194 76 280 22 33 64 128 256), losses := [] }

theorem u24752 : Upper (D 6) (R 6) [34,192,72,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24753 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 297, targets := 64 },{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 194 76 280 22 36 97 161 289), lower := (rows 35 194 76 280 22 36 64 128 256), losses := [] }

theorem u24753 : Upper (D 6) (R 6) [34,192,72,272,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24754 : Route 9 := (fun mask => (mask,id))

def c24754 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24754 : Upper (D 6) (R 6) [34,192,72,272,36,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,36,1] 13 (by decide) (choices 1) [1,2,4] r24754 c24754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7661
  · exact u7662
  · exact u7663

def b24755 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 280 52 34 69 133 261), lower := (rows 35 194 76 280 52 34 64 128 256), losses := [] }

theorem u24755 : Upper (D 6) (R 6) [34,192,72,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24756 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 76 280 52 36 67 131 259), lower := (rows 35 194 76 280 52 36 64 128 256), losses := [] }

theorem u24756 : Upper (D 6) (R 6) [34,192,72,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24757 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 194 76 296 21 33 86 150 278), lower := (rows 35 194 76 296 21 33 64 128 256), losses := [] }

theorem u24757 : Upper (D 6) (R 6) [34,192,72,288,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24758 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 296 21 34 85 149 277), lower := (rows 35 194 76 296 21 34 64 128 256), losses := [] }

theorem u24758 : Upper (D 6) (R 6) [34,192,72,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24759 : Route 9 := (fun mask => (mask,id))

def c24759 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24759 : Upper (D 6) (R 6) [34,192,72,288,5,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,5,4] 13 (by decide) (choices 1) [1,2,16] r24759 c24759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7664
  · exact u7665
  · exact u7666

def r24760 : Route 9 := (fun mask => (mask,id))

def c24760 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24760 : Upper (D 6) (R 6) [34,192,72,288,5,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,5,16] 13 (by decide) (choices 1) [1,2,4] r24760 c24760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7667
  · exact u7668
  · exact u7669

def b24761 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 297, targets := 64 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 194 76 296 22 33 85 149 277), lower := (rows 35 194 76 296 22 33 64 128 256), losses := [] }

theorem u24761 : Upper (D 6) (R 6) [34,192,72,288,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24762 : Route 9 := (fun mask => (mask,id))

def c24762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24762 : Upper (D 6) (R 6) [34,192,72,288,6,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,6,4] 13 (by decide) (choices 1) [1,16] r24762 c24762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7670
  · exact u7671

def b24763 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 76 296 22 48 69 133 261), lower := (rows 35 194 76 296 22 48 64 128 256), losses := [] }

theorem u24763 : Upper (D 6) (R 6) [34,192,72,288,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24763 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24764 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 100 13 26 33 340 404 276), lower := (rows 35 194 100 13 26 33 64 128 256), losses := [] }

theorem u24764 : Upper (D 6) (R 6) [34,192,96,5,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24765 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 100 13 26 36 337 401 273), lower := (rows 35 194 100 13 26 36 64 128 256), losses := [] }

theorem u24765 : Upper (D 6) (R 6) [34,192,96,5,10,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24766 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 100 13 26 48 325 389 261), lower := (rows 35 194 100 13 26 48 64 128 256), losses := [] }

theorem u24766 : Upper (D 6) (R 6) [34,192,96,5,10,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24766 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24767 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 194 100 13 26 288 85 149 277), lower := (rows 35 194 100 13 26 288 64 128 256), losses := [] }

theorem u24767 : Upper (D 6) (R 6) [34,192,96,5,10,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24767 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24768 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 100 13 273 34 92 156 284), lower := (rows 35 194 100 13 273 34 64 128 256), losses := [] }

theorem u24768 : Upper (D 6) (R 6) [34,192,96,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24769 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 100 13 273 36 90 154 282), lower := (rows 35 194 100 13 273 36 64 128 256), losses := [] }

theorem u24769 : Upper (D 6) (R 6) [34,192,96,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24770 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 194 100 13 273 40 86 150 278), lower := (rows 35 194 100 13 273 40 64 128 256), losses := [] }

theorem u24770 : Upper (D 6) (R 6) [34,192,96,5,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24770 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24771 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 194 100 13 273 48 78 142 270), lower := (rows 35 194 100 13 273 48 64 128 256), losses := [] }

theorem u24771 : Upper (D 6) (R 6) [34,192,96,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24771 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24772 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 100 13 274 33 92 156 284), lower := (rows 35 194 100 13 274 33 64 128 256), losses := [] }

theorem u24772 : Upper (D 6) (R 6) [34,192,96,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24773 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 100 13 274 36 89 153 281), lower := (rows 35 194 100 13 274 36 64 128 256), losses := [] }

theorem u24773 : Upper (D 6) (R 6) [34,192,96,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24774 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 194 100 13 274 40 85 149 277), lower := (rows 35 194 100 13 274 40 64 128 256), losses := [] }

theorem u24774 : Upper (D 6) (R 6) [34,192,96,5,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24774 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24775 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 100 13 274 48 77 141 269), lower := (rows 35 194 100 13 274 48 64 128 256), losses := [] }

theorem u24775 : Upper (D 6) (R 6) [34,192,96,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24775 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24776 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 100 13 276 33 90 154 282), lower := (rows 35 194 100 13 276 33 64 128 256), losses := [] }

theorem u24776 : Upper (D 6) (R 6) [34,192,96,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24777 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 100 13 276 34 89 153 281), lower := (rows 35 194 100 13 276 34 64 128 256), losses := [] }

theorem u24777 : Upper (D 6) (R 6) [34,192,96,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24778 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 194 100 13 276 40 83 147 275), lower := (rows 35 194 100 13 276 40 64 128 256), losses := [] }

theorem u24778 : Upper (D 6) (R 6) [34,192,96,5,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24778 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24779 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 194 100 13 276 48 75 139 267), lower := (rows 35 194 100 13 276 48 64 128 256), losses := [] }

theorem u24779 : Upper (D 6) (R 6) [34,192,96,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24779 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24779
end Delivery.IrregularNine14.P06
