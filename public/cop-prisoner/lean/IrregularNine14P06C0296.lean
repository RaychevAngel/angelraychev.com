import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0083
import IrregularNine14P06C0084

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17760 : Route 9 := (fun mask => (mask,id))

def c17760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17760 : Upper (D 6) (R 6) [10,160,257,68,66,16] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,66,16] 13 (by decide) (choices 1) [1,4,32] r17760 c17760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5001
  · exact u5002
  · exact u5003

def r17761 : Route 9 := (fun mask => (mask,id))

def c17761 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17761 : Upper (D 6) (R 6) [10,160,257,68,96,1] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,96,1] 13 (by decide) (choices 1) [2,4,16] r17761 c17761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5004
  · exact u5005
  · exact u5006

def b17762 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 76 112 34 85 149 277), lower := (rows 11 162 261 76 112 34 64 128 256), losses := [] }

theorem u17762 : Upper (D 6) (R 6) [10,160,257,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17763 : Route 9 := (fun mask => (mask,id))

def c17763 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17763 : Upper (D 6) (R 6) [10,160,257,68,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,96,4] 13 (by decide) (choices 1) [1,2,16] r17763 c17763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5007
  · exact u5008
  · exact u5009

def b17764 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 261 76 112 48 71 135 263), lower := (rows 11 162 261 76 112 48 64 128 256), losses := [] }

theorem u17764 : Upper (D 6) (R 6) [10,160,257,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17764 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17765 : Route 9 := (fun mask => (mask,id))

def c17765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17765 : Upper (D 6) (R 6) [10,160,257,80,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,257,80,6,1] 13 (by decide) (choices 1) [4,32] r17765 c17765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5010
  · exact u5011

def r17766 : Route 9 := (fun mask => (mask,id))

def c17766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17766 : Upper (D 6) (R 6) [10,160,257,80,6,4] 13 := by
  apply FastRouting.sound _ _ [10,160,257,80,6,4] 13 (by decide) (choices 1) [1,32] r17766 c17766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5012
  · exact u5013

def r17767 : Route 9 := (fun mask => (mask,id))

def c17767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17767 : Upper (D 6) (R 6) [10,160,257,80,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,257,80,6,64] 13 (by decide) (choices 1) [1,4,32] r17767 c17767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5014
  · exact u5015
  · exact u5016

def b17768 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 162 261 88 52 33 70 198 326), lower := (rows 11 162 261 88 52 33 64 128 256), losses := [] }

theorem u17768 : Upper (D 6) (R 6) [10,160,257,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17769 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 88 52 34 69 197 325), lower := (rows 11 162 261 88 52 34 64 128 256), losses := [] }

theorem u17769 : Upper (D 6) (R 6) [10,160,257,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17770 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 162 261 88 52 36 67 195 323), lower := (rows 11 162 261 88 52 36 64 128 256), losses := [] }

theorem u17770 : Upper (D 6) (R 6) [10,160,257,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17771 : Route 9 := (fun mask => (mask,id))

def c17771 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17771 : Upper (D 6) (R 6) [10,160,257,80,36,64] 13 := by
  apply FastRouting.sound _ _ [10,160,257,80,36,64] 13 (by decide) (choices 1) [1,2,4] r17771 c17771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5017
  · exact u5018
  · exact u5019

def b17772 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 261 104 22 33 84 212 340), lower := (rows 11 162 261 104 22 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 80 144 272), good := (rows 41 160 293 104 508 33 64 128 256) }] }

theorem u17772 : Upper (D 6) (R 6) [10,160,257,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17773 : Route 9 := (fun mask => (mask,id))

def c17773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17773 : Upper (D 6) (R 6) [10,160,257,96,6,4] 13 := by
  apply FastRouting.sound _ _ [10,160,257,96,6,4] 13 (by decide) (choices 1) [1,16] r17773 c17773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5020
  · exact u5021

def b17774 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 261 104 22 48 69 197 325), lower := (rows 11 162 261 104 22 48 64 128 256), losses := [] }

theorem u17774 : Upper (D 6) (R 6) [10,160,257,96,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17774 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17775 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 261 104 22 96 85 149 277), lower := (rows 11 162 261 104 22 96 64 128 256), losses := [] }

theorem u17775 : Upper (D 6) (R 6) [10,160,257,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17776 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 261 104 82 33 84 148 276), lower := (rows 11 162 261 104 82 33 64 128 256), losses := [] }

theorem u17776 : Upper (D 6) (R 6) [10,160,257,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17777 : Route 9 := (fun mask => (mask,id))

def c17777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17777 : Upper (D 6) (R 6) [10,160,257,96,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,257,96,66,4] 13 (by decide) (choices 1) [1,4,16] r17777 c17777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5022
  · exact u5023
  · exact u5024

def b17778 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 261 104 82 48 69 133 261), lower := (rows 11 162 261 104 82 48 64 128 256), losses := [] }

theorem u17778 : Upper (D 6) (R 6) [10,160,257,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17778 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17779 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 261 104 84 33 86 150 278), lower := (rows 11 162 261 104 84 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 64 128 256), good := (rows 41 160 293 104 124 33 64 128 256) }] }

theorem u17779 : Upper (D 6) (R 6) [10,160,257,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17780 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 261 104 84 34 85 149 277), lower := (rows 11 162 261 104 84 34 64 128 256), losses := [] }

theorem u17780 : Upper (D 6) (R 6) [10,160,257,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17781 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 261 104 84 36 83 147 275), lower := (rows 11 162 261 104 84 36 64 128 256), losses := [] }

theorem u17781 : Upper (D 6) (R 6) [10,160,257,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17782 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 261 104 84 48 71 135 263), lower := (rows 11 162 261 104 84 48 64 128 256), losses := [] }

theorem u17782 : Upper (D 6) (R 6) [10,160,257,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17782 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17783 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 162 262 25 52 33 68 196 324), lower := (rows 11 162 262 25 52 33 64 128 256), losses := [] }

theorem u17783 : Upper (D 6) (R 6) [10,160,258,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17784 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 162 262 25 52 36 65 193 321), lower := (rows 11 162 262 25 52 36 64 128 256), losses := [] }

theorem u17784 : Upper (D 6) (R 6) [10,160,258,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17785 : Route 9 := (fun mask => (mask,id))

def c17785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17785 : Upper (D 6) (R 6) [10,160,258,17,36,64] 13 := by
  apply FastRouting.sound _ _ [10,160,258,17,36,64] 13 (by decide) (choices 1) [1,4] r17785 c17785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5025
  · exact u5026

def b17786 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 262 25 84 33 100 228 356), lower := (rows 11 162 262 25 84 33 64 128 256), losses := [] }

theorem u17786 : Upper (D 6) (R 6) [10,160,258,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17787 : Route 9 := (fun mask => (mask,id))

def c17787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17787 : Upper (D 6) (R 6) [10,160,258,17,68,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,17,68,4] 13 (by decide) (choices 1) [1,32] r17787 c17787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5027
  · exact u5028

def r17788 : Route 9 := (fun mask => (mask,id))

def c17788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17788 : Upper (D 6) (R 6) [10,160,258,17,68,64] 13 := by
  apply FastRouting.sound _ _ [10,160,258,17,68,64] 13 (by decide) (choices 1) [1,4,32] r17788 c17788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5029
  · exact u5030
  · exact u5031

def b17789 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 262 25 112 33 68 196 324), lower := (rows 11 162 262 25 112 33 64 128 256), losses := [] }

theorem u17789 : Upper (D 6) (R 6) [10,160,258,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17790 : Route 9 := (fun mask => (mask,id))

def c17790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17790 : Upper (D 6) (R 6) [10,160,258,17,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,17,96,4] 13 (by decide) (choices 1) [1,4] r17790 c17790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5032
  · exact u5033

def b17791 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 262 25 112 96 69 133 261), lower := (rows 11 162 262 25 112 96 64 128 256), losses := [] }

theorem u17791 : Upper (D 6) (R 6) [10,160,258,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17792 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 262 28 49 33 68 196 324), lower := (rows 11 162 262 28 49 33 64 128 256), losses := [] }

theorem u17792 : Upper (D 6) (R 6) [10,160,258,20,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17793 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 162 262 28 49 36 65 193 321), lower := (rows 11 162 262 28 49 36 64 128 256), losses := [] }

theorem u17793 : Upper (D 6) (R 6) [10,160,258,20,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17794 : Route 9 := (fun mask => (mask,id))

def c17794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17794 : Upper (D 6) (R 6) [10,160,258,20,33,64] 13 := by
  apply FastRouting.sound _ _ [10,160,258,20,33,64] 13 (by decide) (choices 1) [1,4] r17794 c17794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5034
  · exact u5035

def b17795 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 262 28 81 33 100 228 356), lower := (rows 11 162 262 28 81 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 39 24 16 32 98 162 290), good := (rows 462 486 454 28 92 486 64 128 256) }] }

theorem u17795 : Upper (D 6) (R 6) [10,160,258,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17796 : Route 9 := (fun mask => (mask,id))

def c17796 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17796 : Upper (D 6) (R 6) [10,160,258,20,65,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,20,65,4] 13 (by decide) (choices 1) [1,32] r17796 c17796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5036
  · exact u5037

def r17797 : Route 9 := (fun mask => (mask,id))

def c17797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17797 : Upper (D 6) (R 6) [10,160,258,20,65,64] 13 := by
  apply FastRouting.sound _ _ [10,160,258,20,65,64] 13 (by decide) (choices 1) [1,4,32] r17797 c17797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5038
  · exact u5039
  · exact u5040

def r17798 : Route 9 := (fun mask => (mask,id))

def c17798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17798 : Upper (D 6) (R 6) [10,160,258,20,96,1] 13 := by
  apply FastRouting.sound _ _ [10,160,258,20,96,1] 13 (by decide) (choices 1) [1,4] r17798 c17798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5041
  · exact u5042

def r17799 : Route 9 := (fun mask => (mask,id))

def c17799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17799 : Upper (D 6) (R 6) [10,160,258,20,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,20,96,4] 13 (by decide) (choices 1) [1] r17799 c17799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u5043

def b17800 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 262 28 112 96 69 133 261), lower := (rows 11 162 262 28 112 96 64 128 256), losses := [] }

theorem u17800 : Upper (D 6) (R 6) [10,160,258,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17801 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 262 44 81 33 84 212 340), lower := (rows 11 162 262 44 81 33 64 128 256), losses := [] }

theorem u17801 : Upper (D 6) (R 6) [10,160,258,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17802 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 262 44 81 36 81 209 337), lower := (rows 11 162 262 44 81 36 64 128 256), losses := [] }

theorem u17802 : Upper (D 6) (R 6) [10,160,258,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17803 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 262 44 81 48 69 197 325), lower := (rows 11 162 262 44 81 48 64 128 256), losses := [] }

theorem u17803 : Upper (D 6) (R 6) [10,160,258,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17803 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17804 : Route 9 := (fun mask => (mask,id))

def c17804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17804 : Upper (D 6) (R 6) [10,160,258,36,65,64] 13 := by
  apply FastRouting.sound _ _ [10,160,258,36,65,64] 13 (by decide) (choices 1) [1,4,16] r17804 c17804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5044
  · exact u5045
  · exact u5046

def b17805 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 262 44 84 33 81 209 337), lower := (rows 11 162 262 44 84 33 64 128 256), losses := [] }

theorem u17805 : Upper (D 6) (R 6) [10,160,258,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17806 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 262 44 84 48 65 193 321), lower := (rows 11 162 262 44 84 48 64 128 256), losses := [] }

theorem u17806 : Upper (D 6) (R 6) [10,160,258,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17806 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17807 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 262 44 84 96 81 145 273), lower := (rows 11 162 262 44 84 96 64 128 256), losses := [] }

theorem u17807 : Upper (D 6) (R 6) [10,160,258,36,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17808 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 162 262 56 81 33 68 196 324), lower := (rows 11 162 262 56 81 33 64 128 256), losses := [] }

theorem u17808 : Upper (D 6) (R 6) [10,160,258,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17809 : Route 9 := (fun mask => (mask,id))

def c17809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17809 : Upper (D 6) (R 6) [10,160,258,48,65,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,48,65,4] 13 (by decide) (choices 1) [1,4] r17809 c17809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5047
  · exact u5048

def b17810 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 262 56 81 96 69 133 261), lower := (rows 11 162 262 56 81 96 64 128 256), losses := [] }

theorem u17810 : Upper (D 6) (R 6) [10,160,258,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17811 : Route 9 := (fun mask => (mask,id))

def c17811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17811 : Upper (D 6) (R 6) [10,160,258,48,68,1] 13 := by
  apply FastRouting.sound _ _ [10,160,258,48,68,1] 13 (by decide) (choices 1) [1,4] r17811 c17811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5049
  · exact u5050

def b17812 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 262 56 84 36 65 193 321), lower := (rows 11 162 262 56 84 36 64 128 256), losses := [] }

theorem u17812 : Upper (D 6) (R 6) [10,160,258,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17813 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 262 56 84 96 69 133 261), lower := (rows 11 162 262 56 84 96 64 128 256), losses := [] }

theorem u17813 : Upper (D 6) (R 6) [10,160,258,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17814 : Route 9 := (fun mask => (mask,id))

def c17814 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17814 : Upper (D 6) (R 6) [10,160,258,65,33,4] 13 := by
  apply FastRouting.sound _ _ [10,160,258,65,33,4] 13 (by decide) (choices 1) [4,16] r17814 c17814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5051
  · exact u5052

def b17815 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 262 73 49 48 68 196 324), lower := (rows 11 162 262 73 49 48 64 128 256), losses := [] }

theorem u17815 : Upper (D 6) (R 6) [10,160,258,65,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17815 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17816 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 48, targets := 6 },{ cop := 4, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 162 262 73 49 96 84 148 276), lower := (rows 11 162 262 73 49 96 64 128 256), losses := [] }

theorem u17816 : Upper (D 6) (R 6) [10,160,258,65,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17817 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 262 73 52 33 84 212 340), lower := (rows 11 162 262 73 52 33 64 128 256), losses := [] }

theorem u17817 : Upper (D 6) (R 6) [10,160,258,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17818 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 162 262 73 52 36 81 209 337), lower := (rows 11 162 262 73 52 36 64 128 256), losses := [] }

theorem u17818 : Upper (D 6) (R 6) [10,160,258,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17819 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 262 73 52 48 69 197 325), lower := (rows 11 162 262 73 52 48 64 128 256), losses := [] }

theorem u17819 : Upper (D 6) (R 6) [10,160,258,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17819 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u17819
end Delivery.IrregularNine14.P06
