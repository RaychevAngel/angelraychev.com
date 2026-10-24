import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0127
import IrregularNine14P06C0128

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24780 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 100 13 280 33 86 150 278), lower := (rows 35 194 100 13 280 33 64 128 256), losses := [] }

theorem u24780 : Upper (D 6) (R 6) [34,192,96,5,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24781 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 100 13 280 34 85 149 277), lower := (rows 35 194 100 13 280 34 64 128 256), losses := [] }

theorem u24781 : Upper (D 6) (R 6) [34,192,96,5,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24782 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 100 13 280 36 83 147 275), lower := (rows 35 194 100 13 280 36 64 128 256), losses := [] }

theorem u24782 : Upper (D 6) (R 6) [34,192,96,5,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24783 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 194 100 13 280 48 71 135 263), lower := (rows 35 194 100 13 280 48 64 128 256), losses := [] }

theorem u24783 : Upper (D 6) (R 6) [34,192,96,5,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24783 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24784 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 305, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 100 14 273 33 92 156 284), lower := (rows 35 194 100 14 273 33 64 128 256), losses := [] }

theorem u24784 : Upper (D 6) (R 6) [34,192,96,6,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24785 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 44, targets := 1 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0)], upper := (rows 35 194 100 14 273 36 89 153 281), lower := (rows 35 194 100 14 273 36 64 128 256), losses := [] }

theorem u24785 : Upper (D 6) (R 6) [34,192,96,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24786 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 100 14 273 40 85 149 277), lower := (rows 35 194 100 14 273 40 64 128 256), losses := [] }

theorem u24786 : Upper (D 6) (R 6) [34,192,96,6,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24786 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24787 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 194 100 14 273 48 77 141 269), lower := (rows 35 194 100 14 273 48 64 128 256), losses := [] }

theorem u24787 : Upper (D 6) (R 6) [34,192,96,6,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24787 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24788 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 305, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 100 14 276 33 89 153 281), lower := (rows 35 194 100 14 276 33 64 128 256), losses := [] }

theorem u24788 : Upper (D 6) (R 6) [34,192,96,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24789 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 100 14 276 40 81 145 273), lower := (rows 35 194 100 14 276 40 64 128 256), losses := [] }

theorem u24789 : Upper (D 6) (R 6) [34,192,96,6,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24789 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24790 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 194 100 14 276 48 73 137 265), lower := (rows 35 194 100 14 276 48 64 128 256), losses := [] }

theorem u24790 : Upper (D 6) (R 6) [34,192,96,6,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24790 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24791 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 305, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 100 14 280 33 85 149 277), lower := (rows 35 194 100 14 280 33 64 128 256), losses := [] }

theorem u24791 : Upper (D 6) (R 6) [34,192,96,6,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24792 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 44, targets := 1 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0)], upper := (rows 35 194 100 14 280 36 81 145 273), lower := (rows 35 194 100 14 280 36 64 128 256), losses := [] }

theorem u24792 : Upper (D 6) (R 6) [34,192,96,6,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24793 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 194 100 14 280 48 69 133 261), lower := (rows 35 194 100 14 280 48 64 128 256), losses := [] }

theorem u24793 : Upper (D 6) (R 6) [34,192,96,6,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24793 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24794 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 194 100 25 28 33 326 390 262), lower := (rows 35 194 100 25 28 33 64 128 256), losses := [] }

theorem u24794 : Upper (D 6) (R 6) [34,192,96,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24795 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 100 25 28 34 325 389 261), lower := (rows 35 194 100 25 28 34 64 128 256), losses := [] }

theorem u24795 : Upper (D 6) (R 6) [34,192,96,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24796 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 450, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 194 100 25 28 36 323 387 259), lower := (rows 35 194 100 25 28 36 64 128 256), losses := [] }

theorem u24796 : Upper (D 6) (R 6) [34,192,96,17,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24797 : Route 9 := (fun mask => (mask,id))

def c24797 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24797 : Upper (D 6) (R 6) [34,192,96,17,12,256] 13 := by
  apply FastRouting.sound _ _ [34,192,96,17,12,256] 13 (by decide) (choices 1) [1,2,4] r24797 c24797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7672
  · exact u7673
  · exact u7674

def b24798 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 194 100 25 274 33 76 140 268), lower := (rows 35 194 100 25 274 33 64 128 256), losses := [] }

theorem u24798 : Upper (D 6) (R 6) [34,192,96,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24799 : Route 9 := (fun mask => (mask,id))

def c24799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24799 : Upper (D 6) (R 6) [34,192,96,17,258,4] 13 := by
  apply FastRouting.sound _ _ [34,192,96,17,258,4] 13 (by decide) (choices 1) [1,4,8] r24799 c24799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7675
  · exact u7676
  · exact u7677

def b24800 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 100 25 274 40 69 133 261), lower := (rows 35 194 100 25 274 40 64 128 256), losses := [] }

theorem u24800 : Upper (D 6) (R 6) [34,192,96,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24800 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24801 : Route 9 := (fun mask => (mask,id))

def c24801 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24801 : Upper (D 6) (R 6) [34,192,96,17,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,96,17,260,1] 13 (by decide) (choices 1) [2,4,8] r24801 c24801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7678
  · exact u7679
  · exact u7680

def b24802 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 100 25 276 34 77 141 269), lower := (rows 35 194 100 25 276 34 64 128 256), losses := [] }

theorem u24802 : Upper (D 6) (R 6) [34,192,96,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24803 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 194, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 194 100 25 276 36 75 139 267), lower := (rows 35 194 100 25 276 36 64 128 256), losses := [] }

theorem u24803 : Upper (D 6) (R 6) [34,192,96,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24804 : Route 9 := (fun mask => (mask,id))

def c24804 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24804 : Upper (D 6) (R 6) [34,192,96,17,260,8] 13 := by
  apply FastRouting.sound _ _ [34,192,96,17,260,8] 13 (by decide) (choices 1) [1,2,4] r24804 c24804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7681
  · exact u7682
  · exact u7683

def b24805 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 198, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 194 100 25 280 33 70 134 262), lower := (rows 35 194 100 25 280 33 64 128 256), losses := [] }

theorem u24805 : Upper (D 6) (R 6) [34,192,96,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24806 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 100 25 280 34 69 133 261), lower := (rows 35 194 100 25 280 34 64 128 256), losses := [] }

theorem u24806 : Upper (D 6) (R 6) [34,192,96,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24807 : Route 9 := (fun mask => (mask,id))

def c24807 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24807 : Upper (D 6) (R 6) [34,192,96,17,264,4] 13 := by
  apply FastRouting.sound _ _ [34,192,96,17,264,4] 13 (by decide) (choices 1) [1,2,4] r24807 c24807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7684
  · exact u7685
  · exact u7686

def b24808 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 194 100 26 28 33 325 389 261), lower := (rows 35 194 100 26 28 33 64 128 256), losses := [] }

theorem u24808 : Upper (D 6) (R 6) [34,192,96,18,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24809 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 60, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 100 26 28 36 321 385 257), lower := (rows 35 194 100 26 28 36 64 128 256), losses := [] }

theorem u24809 : Upper (D 6) (R 6) [34,192,96,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24810 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(0,6),(2,1)], upper := (rows 35 194 100 26 28 288 69 133 261), lower := (rows 35 194 100 26 28 288 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 16 312 0 144 272), good := (rows 35 130 36 443 445 288 0 128 288) }] }

theorem u24810 : Upper (D 6) (R 6) [34,192,96,18,12,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24810 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24811 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 194 100 26 273 33 76 140 268), lower := (rows 35 194 100 26 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 72 136 264), good := (rows 33 192 100 508 305 33 64 128 256) }] }

theorem u24811 : Upper (D 6) (R 6) [34,192,96,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24812 : Route 9 := (fun mask => (mask,id))

def c24812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24812 : Upper (D 6) (R 6) [34,192,96,18,257,4] 13 := by
  apply FastRouting.sound _ _ [34,192,96,18,257,4] 13 (by decide) (choices 1) [1,4,8] r24812 c24812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7687
  · exact u7688
  · exact u7689

def b24813 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 100 26 273 40 69 133 261), lower := (rows 35 194 100 26 273 40 64 128 256), losses := [] }

theorem u24813 : Upper (D 6) (R 6) [34,192,96,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24813 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24814 : Route 9 := (fun mask => (mask,id))

def c24814 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24814 : Upper (D 6) (R 6) [34,192,96,18,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,96,18,260,1] 13 (by decide) (choices 1) [1,4,8] r24814 c24814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7690
  · exact u7691
  · exact u7692

def b24815 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 194 100 26 276 36 73 137 265), lower := (rows 35 194 100 26 276 36 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 16 52 0 136 264), good := (rows 35 130 36 443 308 36 0 128 256) }] }

theorem u24815 : Upper (D 6) (R 6) [34,192,96,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24816 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 100 26 276 40 69 133 261), lower := (rows 35 194 100 26 276 40 64 128 256), losses := [] }

theorem u24816 : Upper (D 6) (R 6) [34,192,96,18,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24816 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24817 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 194 100 26 280 33 69 133 261), lower := (rows 35 194 100 26 280 33 64 128 256), losses := [] }

theorem u24817 : Upper (D 6) (R 6) [34,192,96,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24818 : Route 9 := (fun mask => (mask,id))

def c24818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24818 : Upper (D 6) (R 6) [34,192,96,18,264,4] 13 := by
  apply FastRouting.sound _ _ [34,192,96,18,264,4] 13 (by decide) (choices 1) [1,4] r24818 c24818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7693
  · exact u7694

def b24819 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 194 100 28 273 33 78 142 270), lower := (rows 35 194 100 28 273 33 64 128 256), losses := [] }

theorem u24819 : Upper (D 6) (R 6) [34,192,96,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24820 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 100 28 273 34 77 141 269), lower := (rows 35 194 100 28 273 34 64 128 256), losses := [] }

theorem u24820 : Upper (D 6) (R 6) [34,192,96,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24821 : Route 9 := (fun mask => (mask,id))

def c24821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24821 : Upper (D 6) (R 6) [34,192,96,20,257,4] 13 := by
  apply FastRouting.sound _ _ [34,192,96,20,257,4] 13 (by decide) (choices 1) [1,2,8] r24821 c24821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7695
  · exact u7696
  · exact u7697

def r24822 : Route 9 := (fun mask => (mask,id))

def c24822 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24822 : Upper (D 6) (R 6) [34,192,96,20,257,8] 13 := by
  apply FastRouting.sound _ _ [34,192,96,20,257,8] 13 (by decide) (choices 1) [1,2,4] r24822 c24822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7698
  · exact u7699
  · exact u7700

def r24823 : Route 9 := (fun mask => (mask,id))

def c24823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24823 : Upper (D 6) (R 6) [34,192,96,20,258,1] 13 := by
  apply FastRouting.sound _ _ [34,192,96,20,258,1] 13 (by decide) (choices 1) [1,4,8] r24823 c24823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7701
  · exact u7702
  · exact u7703

def b24824 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 194 100 28 274 36 73 137 265), lower := (rows 35 194 100 28 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 70 24 16 127 64 128 256), good := (rows 38 230 100 60 318 36 100 128 256) }] }

theorem u24824 : Upper (D 6) (R 6) [34,192,96,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24825 : Route 9 := (fun mask => (mask,id))

def c24825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24825 : Upper (D 6) (R 6) [34,192,96,20,258,8] 13 := by
  apply FastRouting.sound _ _ [34,192,96,20,258,8] 13 (by decide) (choices 1) [1,4] r24825 c24825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7704
  · exact u7705

def r24826 : Route 9 := (fun mask => (mask,id))

def c24826 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24826 : Upper (D 6) (R 6) [34,192,96,20,264,1] 13 := by
  apply FastRouting.sound _ _ [34,192,96,20,264,1] 13 (by decide) (choices 1) [1,2,4] r24826 c24826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7706
  · exact u7707
  · exact u7708

def b24827 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 100 28 280 34 69 133 261), lower := (rows 35 194 100 28 280 34 64 128 256), losses := [] }

theorem u24827 : Upper (D 6) (R 6) [34,192,96,20,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24828 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 194, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 194 100 28 280 36 67 131 259), lower := (rows 35 194 100 28 280 36 64 128 256), losses := [] }

theorem u24828 : Upper (D 6) (R 6) [34,192,96,20,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24829 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 49, targets := 64 },{ cop := 4, region := 356, targets := 2 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 35 194 261 14 25 36 112 240 368), lower := (rows 35 194 261 14 25 36 64 128 256), losses := [] }

theorem u24829 : Upper (D 6) (R 6) [34,192,257,6,9,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24830 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 261 14 25 48 100 228 356), lower := (rows 35 194 261 14 25 48 64 128 256), losses := [] }

theorem u24830 : Upper (D 6) (R 6) [34,192,257,6,9,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24830 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24831 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 261 14 25 96 116 180 308), lower := (rows 35 194 261 14 25 96 64 128 256), losses := [] }

theorem u24831 : Upper (D 6) (R 6) [34,192,257,6,9,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24832 : PairBound 9 := { available := 88, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 261 14 52 33 88 216 344), lower := (rows 35 194 261 14 52 33 64 128 256), losses := [] }

theorem u24832 : Upper (D 6) (R 6) [34,192,257,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24833 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 261 14 52 40 81 209 337), lower := (rows 35 194 261 14 52 40 64 128 256), losses := [] }

theorem u24833 : Upper (D 6) (R 6) [34,192,257,6,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24833 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24834 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 261 14 52 48 73 201 329), lower := (rows 35 194 261 14 52 48 64 128 256), losses := [] }

theorem u24834 : Upper (D 6) (R 6) [34,192,257,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24834 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24835 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 261 14 52 96 89 153 281), lower := (rows 35 194 261 14 52 96 64 128 256), losses := [] }

theorem u24835 : Upper (D 6) (R 6) [34,192,257,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24836 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 261 14 56 33 84 212 340), lower := (rows 35 194 261 14 56 33 64 128 256), losses := [] }

theorem u24836 : Upper (D 6) (R 6) [34,192,257,6,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24837 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 194 261 14 56 36 81 209 337), lower := (rows 35 194 261 14 56 36 64 128 256), losses := [] }

theorem u24837 : Upper (D 6) (R 6) [34,192,257,6,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24838 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 261 14 56 48 69 197 325), lower := (rows 35 194 261 14 56 48 64 128 256), losses := [] }

theorem u24838 : Upper (D 6) (R 6) [34,192,257,6,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24838 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24839 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 261 14 56 96 85 149 277), lower := (rows 35 194 261 14 56 96 64 128 256), losses := [] }

theorem u24839 : Upper (D 6) (R 6) [34,192,257,6,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24839
end Delivery.IrregularNine14.P06
