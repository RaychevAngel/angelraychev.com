import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0284
import IrregularNine14P06C0285

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33780 : Route 9 := (fun mask => (mask,id))

def c33780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33780 : Upper (D 6) (R 6) [10,160,18,68,260] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,260] 13 (by decide) (choices 1) [1,64] r33780 c33780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17040
  · exact u17041

def r33781 : Route 9 := (fun mask => (mask,id))

def c33781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33781 : Upper (D 6) (R 6) [10,160,18,68,288] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,288] 13 (by decide) (choices 1) [1,4,64] r33781 c33781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17042
  · exact u17043
  · exact u17044

def r33782 : Route 9 := (fun mask => (mask,id))

def c33782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33782 : Upper (D 6) (R 6) [10,160,18,68,320] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,320] 13 (by decide) (choices 1) [1,4] r33782 c33782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17045
  · exact u17046

def r33783 : Route 9 := (fun mask => (mask,id))

def c33783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33783 : Upper (D 6) (R 6) [10,160,18,96,257] 13 := by
  apply FastRouting.sound _ _ [10,160,18,96,257] 13 (by decide) (choices 1) [1,4,64] r33783 c33783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17047
  · exact u17048
  · exact u17049

def r33784 : Route 9 := (fun mask => (mask,id))

def c33784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33784 : Upper (D 6) (R 6) [10,160,18,96,260] 13 := by
  apply FastRouting.sound _ _ [10,160,18,96,260] 13 (by decide) (choices 1) [1,4,64] r33784 c33784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17050
  · exact u17051
  · exact u17052

def r33785 : Route 9 := (fun mask => (mask,id))

def c33785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33785 : Upper (D 6) (R 6) [10,160,18,96,320] 13 := by
  apply FastRouting.sound _ _ [10,160,18,96,320] 13 (by decide) (choices 1) [1,4] r33785 c33785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17053
  · exact u17054

def b33786 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 37 25 22 356 324 452 324), lower := (rows 11 162 37 25 22 32 64 128 256), losses := [] }

theorem u33786 : Upper (D 6) (R 6) [10,160,33,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33787 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 37 25 82 356 324 452 324), lower := (rows 11 162 37 25 82 32 64 128 256), losses := [] }

theorem u33787 : Upper (D 6) (R 6) [10,160,33,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33788 : Route 9 := (fun mask => (mask,id))

def c33788 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33788 : Upper (D 6) (R 6) [10,160,33,17,68] 13 := by
  apply FastRouting.sound _ _ [10,160,33,17,68] 13 (by decide) (choices 1) [2,4,64,256] r33788 c33788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17055
  · exact u17056
  · exact u17057
  · exact u17058

def b33789 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 37 25 274 100 68 196 324), lower := (rows 11 162 37 25 274 32 64 128 256), losses := [] }

theorem u33789 : Upper (D 6) (R 6) [10,160,33,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33790 : Route 9 := (fun mask => (mask,id))

def c33790 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33790 : Upper (D 6) (R 6) [10,160,33,17,260] 13 := by
  apply FastRouting.sound _ _ [10,160,33,17,260] 13 (by decide) (choices 1) [2,4,64] r33790 c33790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17059
  · exact u17060
  · exact u17061

def r33791 : Route 9 := (fun mask => (mask,id))

def c33791 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33791 : Upper (D 6) (R 6) [10,160,33,17,320] 13 := by
  apply FastRouting.sound _ _ [10,160,33,17,320] 13 (by decide) (choices 1) [2,4,64] r33791 c33791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17062
  · exact u17063
  · exact u17064

def b33792 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 37 28 19 356 324 452 324), lower := (rows 11 162 37 28 19 32 64 128 256), losses := [] }

theorem u33792 : Upper (D 6) (R 6) [10,160,33,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33793 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 162 37 28 21 354 322 450 322), lower := (rows 11 162 37 28 21 32 64 128 256), losses := [] }

theorem u33793 : Upper (D 6) (R 6) [10,160,33,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33794 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 37 28 22 353 321 449 321), lower := (rows 11 162 37 28 22 32 64 128 256), losses := [] }

theorem u33794 : Upper (D 6) (R 6) [10,160,33,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33795 : Route 9 := (fun mask => (mask,id))

def c33795 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33795 : Upper (D 6) (R 6) [10,160,33,20,65] 13 := by
  apply FastRouting.sound _ _ [10,160,33,20,65] 13 (by decide) (choices 1) [2,4,64,256] r33795 c33795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17065
  · exact u17066
  · exact u17067
  · exact u17068

def r33796 : Route 9 := (fun mask => (mask,id))

def c33796 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33796 : Upper (D 6) (R 6) [10,160,33,20,66] 13 := by
  apply FastRouting.sound _ _ [10,160,33,20,66] 13 (by decide) (choices 1) [1,4,64,256] r33796 c33796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17069
  · exact u17070
  · exact u17071
  · exact u17072

def b33797 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 37 28 84 355 323 451 323), lower := (rows 11 162 37 28 84 32 64 128 256), losses := [] }

theorem u33797 : Upper (D 6) (R 6) [10,160,33,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33798 : Route 9 := (fun mask => (mask,id))

def c33798 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33798 : Upper (D 6) (R 6) [10,160,33,20,257] 13 := by
  apply FastRouting.sound _ _ [10,160,33,20,257] 13 (by decide) (choices 1) [2,4,64] r33798 c33798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17073
  · exact u17074
  · exact u17075

def r33799 : Route 9 := (fun mask => (mask,id))

def c33799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33799 : Upper (D 6) (R 6) [10,160,33,20,258] 13 := by
  apply FastRouting.sound _ _ [10,160,33,20,258] 13 (by decide) (choices 1) [1,4,64] r33799 c33799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17076
  · exact u17077
  · exact u17078

def b33800 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 37 28 276 99 67 195 323), lower := (rows 11 162 37 28 276 32 64 128 256), losses := [] }

theorem u33800 : Upper (D 6) (R 6) [10,160,33,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33801 : Route 9 := (fun mask => (mask,id))

def c33801 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33801 : Upper (D 6) (R 6) [10,160,33,20,320] 13 := by
  apply FastRouting.sound _ _ [10,160,33,20,320] 13 (by decide) (choices 1) [1,2,4,64] r33801 c33801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17079
  · exact u17080
  · exact u17081
  · exact u17082

def b33802 : PairBound 9 := { available := 340, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(1,0),(4,0)], upper := (rows 11 162 37 73 22 372 340 468 340), lower := (rows 11 162 37 73 22 32 64 128 256), losses := [] }

theorem u33802 : Upper (D 6) (R 6) [10,160,33,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33803 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 37 73 82 308 340 404 276), lower := (rows 11 162 37 73 82 32 64 128 256), losses := [] }

theorem u33803 : Upper (D 6) (R 6) [10,160,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33804 : PairBound 9 := { available := 278, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 162 37 73 84 310 342 406 278), lower := (rows 11 162 37 73 84 32 64 128 256), losses := [] }

theorem u33804 : Upper (D 6) (R 6) [10,160,33,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33805 : Route 9 := (fun mask => (mask,id))

def c33805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33805 : Upper (D 6) (R 6) [10,160,33,65,258] 13 := by
  apply FastRouting.sound _ _ [10,160,33,65,258] 13 (by decide) (choices 1) [4,16,64] r33805 c33805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17083
  · exact u17084
  · exact u17085

def r33806 : Route 9 := (fun mask => (mask,id))

def c33806 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33806 : Upper (D 6) (R 6) [10,160,33,65,260] 13 := by
  apply FastRouting.sound _ _ [10,160,33,65,260] 13 (by decide) (choices 1) [2,4,16,64] r33806 c33806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17086
  · exact u17087
  · exact u17088
  · exact u17089

def r33807 : Route 9 := (fun mask => (mask,id))

def c33807 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33807 : Upper (D 6) (R 6) [10,160,33,65,320] 13 := by
  apply FastRouting.sound _ _ [10,160,33,65,320] 13 (by decide) (choices 1) [2,4,16] r33807 c33807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17090
  · exact u17091
  · exact u17092

def b33808 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 37 76 19 372 340 468 340), lower := (rows 11 162 37 76 19 32 64 128 256), losses := [] }

theorem u33808 : Upper (D 6) (R 6) [10,160,33,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33809 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 37 76 21 370 338 466 338), lower := (rows 11 162 37 76 21 32 64 128 256), losses := [] }

theorem u33809 : Upper (D 6) (R 6) [10,160,33,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33810 : Route 9 := (fun mask => (mask,id))

def c33810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u33810 : Upper (D 6) (R 6) [10,160,33,68,6] 13 := by
  apply FastRouting.sound _ _ [10,160,33,68,6] 13 (by decide) (choices 1) [1,16,64,256] r33810 c33810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17093
  · exact u17094
  · exact u17095
  · exact u17096

def r33811 : Route 9 := (fun mask => (mask,id))

def c33811 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33811 : Upper (D 6) (R 6) [10,160,33,68,65] 13 := by
  apply FastRouting.sound _ _ [10,160,33,68,65] 13 (by decide) (choices 1) [2,4,16,256] r33811 c33811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17097
  · exact u17098
  · exact u17099
  · exact u17100

def r33812 : Route 9 := (fun mask => (mask,id))

def c33812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33812 : Upper (D 6) (R 6) [10,160,33,68,66] 13 := by
  apply FastRouting.sound _ _ [10,160,33,68,66] 13 (by decide) (choices 1) [1,4,16,256] r33812 c33812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17101
  · exact u17102
  · exact u17103
  · exact u17104

def b33813 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 37 76 84 307 339 403 275), lower := (rows 11 162 37 76 84 32 64 128 256), losses := [] }

theorem u33813 : Upper (D 6) (R 6) [10,160,33,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33814 : Route 9 := (fun mask => (mask,id))

def c33814 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33814 : Upper (D 6) (R 6) [10,160,33,68,257] 13 := by
  apply FastRouting.sound _ _ [10,160,33,68,257] 13 (by decide) (choices 1) [2,4,16,64] r33814 c33814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17105
  · exact u17106
  · exact u17107
  · exact u17108

def r33815 : Route 9 := (fun mask => (mask,id))

def c33815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33815 : Upper (D 6) (R 6) [10,160,33,68,258] 13 := by
  apply FastRouting.sound _ _ [10,160,33,68,258] 13 (by decide) (choices 1) [1,4,16,64] r33815 c33815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17109
  · exact u17110
  · exact u17111
  · exact u17112

def r33816 : Route 9 := (fun mask => (mask,id))

def c33816 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33816 : Upper (D 6) (R 6) [10,160,33,68,260] 13 := by
  apply FastRouting.sound _ _ [10,160,33,68,260] 13 (by decide) (choices 1) [1,2,16,64] r33816 c33816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17113
  · exact u17114
  · exact u17115
  · exact u17116

def r33817 : Route 9 := (fun mask => (mask,id))

def c33817 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33817 : Upper (D 6) (R 6) [10,160,33,68,320] 13 := by
  apply FastRouting.sound _ _ [10,160,33,68,320] 13 (by decide) (choices 1) [1,2,4,16] r33817 c33817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17117
  · exact u17118
  · exact u17119
  · exact u17120

def b33818 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 37 88 19 356 324 452 324), lower := (rows 11 162 37 88 19 32 64 128 256), losses := [] }

theorem u33818 : Upper (D 6) (R 6) [10,160,33,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33819 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 37 88 21 358 326 454 326), lower := (rows 11 162 37 88 21 32 64 128 256), losses := [] }

theorem u33819 : Upper (D 6) (R 6) [10,160,33,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33820 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 329, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 162 37 88 22 357 325 453 325), lower := (rows 11 162 37 88 22 32 64 128 256), losses := [] }

theorem u33820 : Upper (D 6) (R 6) [10,160,33,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33821 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 162 37 88 81 294 326 390 262), lower := (rows 11 162 37 88 81 32 64 128 256), losses := [] }

theorem u33821 : Upper (D 6) (R 6) [10,160,33,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33822 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 37 88 82 293 325 389 261), lower := (rows 11 162 37 88 82 32 64 128 256), losses := [] }

theorem u33822 : Upper (D 6) (R 6) [10,160,33,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33823 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 162 37 88 84 295 327 391 263), lower := (rows 11 162 37 88 84 32 64 128 256), losses := [] }

theorem u33823 : Upper (D 6) (R 6) [10,160,33,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33824 : Route 9 := (fun mask => (mask,id))

def c33824 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33824 : Upper (D 6) (R 6) [10,160,33,80,257] 13 := by
  apply FastRouting.sound _ _ [10,160,33,80,257] 13 (by decide) (choices 1) [2,4,64] r33824 c33824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17121
  · exact u17122
  · exact u17123

def r33825 : Route 9 := (fun mask => (mask,id))

def c33825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33825 : Upper (D 6) (R 6) [10,160,33,80,258] 13 := by
  apply FastRouting.sound _ _ [10,160,33,80,258] 13 (by decide) (choices 1) [1,4,64] r33825 c33825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17124
  · exact u17125
  · exact u17126

def r33826 : Route 9 := (fun mask => (mask,id))

def c33826 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33826 : Upper (D 6) (R 6) [10,160,33,80,260] 13 := by
  apply FastRouting.sound _ _ [10,160,33,80,260] 13 (by decide) (choices 1) [1,2,4,64] r33826 c33826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17127
  · exact u17128
  · exact u17129
  · exact u17130

def b33827 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 162 37 88 336 39 71 135 263), lower := (rows 11 162 37 88 336 32 64 128 256), losses := [] }

theorem u33827 : Upper (D 6) (R 6) [10,160,33,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33828 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(1,0),(4,0)], upper := (rows 11 162 37 265 22 116 84 212 340), lower := (rows 11 162 37 265 22 32 64 128 256), losses := [] }

theorem u33828 : Upper (D 6) (R 6) [10,160,33,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33829 : Route 9 := (fun mask => (mask,id))

def c33829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33829 : Upper (D 6) (R 6) [10,160,33,257,66] 13 := by
  apply FastRouting.sound _ _ [10,160,33,257,66] 13 (by decide) (choices 1) [4,16,64] r33829 c33829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17131
  · exact u17132
  · exact u17133

def r33830 : Route 9 := (fun mask => (mask,id))

def c33830 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33830 : Upper (D 6) (R 6) [10,160,33,257,68] 13 := by
  apply FastRouting.sound _ _ [10,160,33,257,68] 13 (by decide) (choices 1) [2,4,16,64] r33830 c33830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17134
  · exact u17135
  · exact u17136
  · exact u17137

def b33831 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 37 268 19 116 84 212 340), lower := (rows 11 162 37 268 19 32 64 128 256), losses := [] }

theorem u33831 : Upper (D 6) (R 6) [10,160,33,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33832 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 37 268 21 114 82 210 338), lower := (rows 11 162 37 268 21 32 64 128 256), losses := [] }

theorem u33832 : Upper (D 6) (R 6) [10,160,33,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33833 : Route 9 := (fun mask => (mask,id))

def c33833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33833 : Upper (D 6) (R 6) [10,160,33,260,6] 13 := by
  apply FastRouting.sound _ _ [10,160,33,260,6] 13 (by decide) (choices 1) [1,16,64] r33833 c33833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17138
  · exact u17139
  · exact u17140

def r33834 : Route 9 := (fun mask => (mask,id))

def c33834 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33834 : Upper (D 6) (R 6) [10,160,33,260,65] 13 := by
  apply FastRouting.sound _ _ [10,160,33,260,65] 13 (by decide) (choices 1) [2,4,16,64] r33834 c33834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17141
  · exact u17142
  · exact u17143
  · exact u17144

def r33835 : Route 9 := (fun mask => (mask,id))

def c33835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33835 : Upper (D 6) (R 6) [10,160,33,260,66] 13 := by
  apply FastRouting.sound _ _ [10,160,33,260,66] 13 (by decide) (choices 1) [1,4,16,64] r33835 c33835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17145
  · exact u17146
  · exact u17147
  · exact u17148

def r33836 : Route 9 := (fun mask => (mask,id))

def c33836 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33836 : Upper (D 6) (R 6) [10,160,33,260,68] 13 := by
  apply FastRouting.sound _ _ [10,160,33,260,68] 13 (by decide) (choices 1) [1,2,16,64] r33836 c33836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17149
  · exact u17150
  · exact u17151
  · exact u17152

def b33837 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 37 280 19 100 68 196 324), lower := (rows 11 162 37 280 19 32 64 128 256), losses := [] }

theorem u33837 : Upper (D 6) (R 6) [10,160,33,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33838 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 37 280 21 102 70 198 326), lower := (rows 11 162 37 280 21 32 64 128 256), losses := [] }

theorem u33838 : Upper (D 6) (R 6) [10,160,33,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33839 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 329, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 162 37 280 22 101 69 197 325), lower := (rows 11 162 37 280 22 32 64 128 256), losses := [] }

theorem u33839 : Upper (D 6) (R 6) [10,160,33,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u33839
end Delivery.IrregularNine14.P06
