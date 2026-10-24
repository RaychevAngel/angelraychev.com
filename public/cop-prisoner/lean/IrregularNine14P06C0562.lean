import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0282
import IrregularNine14P06C0283

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33720 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 292 41 19 100 68 196 324), lower := (rows 11 146 292 41 19 32 64 128 256), losses := [] }

theorem u33720 : Upper (D 6) (R 6) [10,144,288,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33721 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 146 292 41 21 102 70 198 326), lower := (rows 11 146 292 41 21 32 64 128 256), losses := [] }

theorem u33721 : Upper (D 6) (R 6) [10,144,288,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33722 : Route 9 := (fun mask => (mask,id))

def c33722 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33722 : Upper (D 6) (R 6) [10,144,288,33,6] 13 := by
  apply FastRouting.sound _ _ [10,144,288,33,6] 13 (by decide) (choices 1) [1,4,64] r33722 c33722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16952
  · exact u16953
  · exact u16954

def r33723 : Route 9 := (fun mask => (mask,id))

def c33723 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33723 : Upper (D 6) (R 6) [10,144,288,33,65] 13 := by
  apply FastRouting.sound _ _ [10,144,288,33,65] 13 (by decide) (choices 1) [2,4,64] r33723 c33723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16955
  · exact u16956
  · exact u16957

def r33724 : Route 9 := (fun mask => (mask,id))

def c33724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33724 : Upper (D 6) (R 6) [10,144,288,33,66] 13 := by
  apply FastRouting.sound _ _ [10,144,288,33,66] 13 (by decide) (choices 1) [1,4,64] r33724 c33724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16958
  · exact u16959
  · exact u16960

def r33725 : Route 9 := (fun mask => (mask,id))

def c33725 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33725 : Upper (D 6) (R 6) [10,144,288,33,68] 13 := by
  apply FastRouting.sound _ _ [10,144,288,33,68] 13 (by decide) (choices 1) [1,2,4,64] r33725 c33725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16961
  · exact u16962
  · exact u16963
  · exact u16964

def b33726 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 292 73 19 100 100 228 356), lower := (rows 11 146 292 73 19 32 64 128 256), losses := [] }

theorem u33726 : Upper (D 6) (R 6) [10,144,288,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33727 : Route 9 := (fun mask => (mask,id))

def c33727 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33727 : Upper (D 6) (R 6) [10,144,288,65,5] 13 := by
  apply FastRouting.sound _ _ [10,144,288,65,5] 13 (by decide) (choices 1) [2,4,64] r33727 c33727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16965
  · exact u16966
  · exact u16967

def r33728 : Route 9 := (fun mask => (mask,id))

def c33728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33728 : Upper (D 6) (R 6) [10,144,288,65,6] 13 := by
  apply FastRouting.sound _ _ [10,144,288,65,6] 13 (by decide) (choices 1) [1,4,64] r33728 c33728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16968
  · exact u16969
  · exact u16970

def r33729 : Route 9 := (fun mask => (mask,id))

def c33729 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33729 : Upper (D 6) (R 6) [10,144,288,65,33] 13 := by
  apply FastRouting.sound _ _ [10,144,288,65,33] 13 (by decide) (choices 1) [2,4,64] r33729 c33729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16971
  · exact u16972
  · exact u16973

def r33730 : Route 9 := (fun mask => (mask,id))

def c33730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33730 : Upper (D 6) (R 6) [10,144,288,65,34] 13 := by
  apply FastRouting.sound _ _ [10,144,288,65,34] 13 (by decide) (choices 1) [1,4,64] r33730 c33730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16974
  · exact u16975
  · exact u16976

def b33731 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 292 73 52 103 71 199 327), lower := (rows 11 146 292 73 52 32 64 128 256), losses := [] }

theorem u33731 : Upper (D 6) (R 6) [10,144,288,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33732 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 146 292 73 81 38 102 166 294), lower := (rows 11 146 292 73 81 32 64 128 256), losses := [] }

theorem u33732 : Upper (D 6) (R 6) [10,144,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33733 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 146 292 73 82 37 101 165 293), lower := (rows 11 146 292 73 82 32 64 128 256), losses := [] }

theorem u33733 : Upper (D 6) (R 6) [10,144,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33734 : Route 9 := (fun mask => (mask,id))

def c33734 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33734 : Upper (D 6) (R 6) [10,144,288,65,68] 13 := by
  apply FastRouting.sound _ _ [10,144,288,65,68] 13 (by decide) (choices 1) [1,2,4] r33734 c33734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16977
  · exact u16978
  · exact u16979

def r33735 : Route 9 := (fun mask => (mask,id))

def c33735 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33735 : Upper (D 6) (R 6) [10,144,288,65,96] 13 := by
  apply FastRouting.sound _ _ [10,144,288,65,96] 13 (by decide) (choices 1) [1,2,4] r33735 c33735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16980
  · exact u16981
  · exact u16982

def b33736 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 292 76 19 101 101 229 357), lower := (rows 11 146 292 76 19 32 64 128 256), losses := [] }

theorem u33736 : Upper (D 6) (R 6) [10,144,288,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33737 : Route 9 := (fun mask => (mask,id))

def c33737 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33737 : Upper (D 6) (R 6) [10,144,288,68,5] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,5] 13 (by decide) (choices 1) [1,2,64] r33737 c33737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16983
  · exact u16984
  · exact u16985

def r33738 : Route 9 := (fun mask => (mask,id))

def c33738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33738 : Upper (D 6) (R 6) [10,144,288,68,6] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,6] 13 (by decide) (choices 1) [1,64] r33738 c33738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16986
  · exact u16987

def r33739 : Route 9 := (fun mask => (mask,id))

def c33739 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33739 : Upper (D 6) (R 6) [10,144,288,68,33] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,33] 13 (by decide) (choices 1) [1,2,4,64] r33739 c33739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16988
  · exact u16989
  · exact u16990
  · exact u16991

def r33740 : Route 9 := (fun mask => (mask,id))

def c33740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33740 : Upper (D 6) (R 6) [10,144,288,68,34] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,34] 13 (by decide) (choices 1) [1,4,64] r33740 c33740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16992
  · exact u16993
  · exact u16994

def b33741 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 292 76 52 99 67 195 323), lower := (rows 11 146 292 76 52 32 64 128 256), losses := [] }

theorem u33741 : Upper (D 6) (R 6) [10,144,288,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33742 : Route 9 := (fun mask => (mask,id))

def c33742 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33742 : Upper (D 6) (R 6) [10,144,288,68,65] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,65] 13 (by decide) (choices 1) [1,2,4] r33742 c33742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16995
  · exact u16996
  · exact u16997

def b33743 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 292, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 146 292 76 82 37 101 165 293), lower := (rows 11 146 292 76 82 32 64 128 256), losses := [] }

theorem u33743 : Upper (D 6) (R 6) [10,144,288,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33744 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 146 292 76 84 35 99 163 291), lower := (rows 11 146 292 76 84 32 64 128 256), losses := [] }

theorem u33744 : Upper (D 6) (R 6) [10,144,288,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33745 : Route 9 := (fun mask => (mask,id))

def c33745 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33745 : Upper (D 6) (R 6) [10,144,288,68,96] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,96] 13 (by decide) (choices 1) [1,2,4] r33745 c33745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16998
  · exact u16999
  · exact u17000

def b33746 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 292 104 19 101 69 197 325), lower := (rows 11 146 292 104 19 32 64 128 256), losses := [] }

theorem u33746 : Upper (D 6) (R 6) [10,144,288,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33747 : Route 9 := (fun mask => (mask,id))

def c33747 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33747 : Upper (D 6) (R 6) [10,144,288,96,5] 13 := by
  apply FastRouting.sound _ _ [10,144,288,96,5] 13 (by decide) (choices 1) [1,2,4,64] r33747 c33747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17001
  · exact u17002
  · exact u17003
  · exact u17004

def r33748 : Route 9 := (fun mask => (mask,id))

def c33748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33748 : Upper (D 6) (R 6) [10,144,288,96,6] 13 := by
  apply FastRouting.sound _ _ [10,144,288,96,6] 13 (by decide) (choices 1) [1,4,64] r33748 c33748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17005
  · exact u17006
  · exact u17007

def r33749 : Route 9 := (fun mask => (mask,id))

def c33749 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33749 : Upper (D 6) (R 6) [10,144,288,96,65] 13 := by
  apply FastRouting.sound _ _ [10,144,288,96,65] 13 (by decide) (choices 1) [1,2,4] r33749 c33749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17008
  · exact u17009
  · exact u17010

def b33750 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 292, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 146 292 104 82 37 69 133 261), lower := (rows 11 146 292 104 82 32 64 128 256), losses := [] }

theorem u33750 : Upper (D 6) (R 6) [10,144,288,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33751 : Route 9 := (fun mask => (mask,id))

def c33751 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33751 : Upper (D 6) (R 6) [10,144,288,96,68] 13 := by
  apply FastRouting.sound _ _ [10,144,288,96,68] 13 (by decide) (choices 1) [1,2,4] r33751 c33751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17011
  · exact u17012
  · exact u17013

def b33752 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 22 13 49 356 324 452 324), lower := (rows 11 162 22 13 49 32 64 128 256), losses := [] }

theorem u33752 : Upper (D 6) (R 6) [10,160,18,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33753 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 22 13 81 356 356 484 356), lower := (rows 11 162 22 13 81 32 64 128 256), losses := [] }

theorem u33753 : Upper (D 6) (R 6) [10,160,18,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33754 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 22 13 84 353 353 481 353), lower := (rows 11 162 22 13 84 32 64 128 256), losses := [] }

theorem u33754 : Upper (D 6) (R 6) [10,160,18,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33755 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 9, targets := 32 },{ cop := 2, region := 9, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 22 13 112 357 325 453 325), lower := (rows 11 162 22 13 112 32 64 128 256), losses := [] }

theorem u33755 : Upper (D 6) (R 6) [10,160,18,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33756 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 22 13 273 100 100 228 356), lower := (rows 11 162 22 13 273 32 64 128 256), losses := [] }

theorem u33756 : Upper (D 6) (R 6) [10,160,18,5,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33757 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 22 13 276 97 97 225 353), lower := (rows 11 162 22 13 276 32 64 128 256), losses := [] }

theorem u33757 : Upper (D 6) (R 6) [10,160,18,5,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33758 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 9, targets := 32 },{ cop := 2, region := 9, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 22 13 304 101 69 197 325), lower := (rows 11 162 22 13 304 32 64 128 256), losses := [] }

theorem u33758 : Upper (D 6) (R 6) [10,160,18,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33759 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 22 13 336 101 101 229 357), lower := (rows 11 162 22 13 336 32 64 128 256), losses := [] }

theorem u33759 : Upper (D 6) (R 6) [10,160,18,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33760 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 22 41 81 356 324 452 324), lower := (rows 11 162 22 41 81 32 64 128 256), losses := [] }

theorem u33760 : Upper (D 6) (R 6) [10,160,18,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33761 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 22 41 84 357 325 453 325), lower := (rows 11 162 22 41 84 32 64 128 256), losses := [] }

theorem u33761 : Upper (D 6) (R 6) [10,160,18,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33762 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 22 41 273 100 68 196 324), lower := (rows 11 162 22 41 273 32 64 128 256), losses := [] }

theorem u33762 : Upper (D 6) (R 6) [10,160,18,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33763 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 22 41 276 101 69 197 325), lower := (rows 11 162 22 41 276 32 64 128 256), losses := [] }

theorem u33763 : Upper (D 6) (R 6) [10,160,18,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33764 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 22 41 336 101 69 197 325), lower := (rows 11 162 22 41 336 32 64 128 256), losses := [] }

theorem u33764 : Upper (D 6) (R 6) [10,160,18,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33765 : Route 9 := (fun mask => (mask,id))

def c33765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33765 : Upper (D 6) (R 6) [10,160,18,36,65] 13 := by
  apply FastRouting.sound _ _ [10,160,18,36,65] 13 (by decide) (choices 1) [1,4,64,256] r33765 c33765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17014
  · exact u17015
  · exact u17016
  · exact u17017

def b33766 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 451, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 22 44 84 353 321 449 321), lower := (rows 11 162 22 44 84 32 64 128 256), losses := [] }

theorem u33766 : Upper (D 6) (R 6) [10,160,18,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33767 : Route 9 := (fun mask => (mask,id))

def c33767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33767 : Upper (D 6) (R 6) [10,160,18,36,257] 13 := by
  apply FastRouting.sound _ _ [10,160,18,36,257] 13 (by decide) (choices 1) [1,4,64] r33767 c33767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17018
  · exact u17019
  · exact u17020

def b33768 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 22 44 276 97 65 193 321), lower := (rows 11 162 22 44 276 32 64 128 256), losses := [] }

theorem u33768 : Upper (D 6) (R 6) [10,160,18,36,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33769 : Route 9 := (fun mask => (mask,id))

def c33769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33769 : Upper (D 6) (R 6) [10,160,18,36,320] 13 := by
  apply FastRouting.sound _ _ [10,160,18,36,320] 13 (by decide) (choices 1) [1,4,64] r33769 c33769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17021
  · exact u17022
  · exact u17023

def b33770 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 162 22 73 81 292 356 420 292), lower := (rows 11 162 22 73 81 32 64 128 256), losses := [] }

theorem u33770 : Upper (D 6) (R 6) [10,160,18,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33771 : PairBound 9 := { available := 293, camps := [], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 162 22 73 84 293 357 421 293), lower := (rows 11 162 22 73 84 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 24 32 64 128 256), good := (rows 30 162 22 92 84 32 64 128 256) },{ target := 2, region := (rows 5 2 0 24 16 32 64 128 256), good := (rows 11 162 27 73 89 32 64 128 256) }] }

theorem u33771 : Upper (D 6) (R 6) [10,160,18,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33772 : Route 9 := (fun mask => (mask,id))

def c33772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33772 : Upper (D 6) (R 6) [10,160,18,65,96] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,96] 13 (by decide) (choices 1) [1,4,256] r33772 c33772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17024
  · exact u17025
  · exact u17026

def r33773 : Route 9 := (fun mask => (mask,id))

def c33773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33773 : Upper (D 6) (R 6) [10,160,18,65,257] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,257] 13 (by decide) (choices 1) [4,64] r33773 c33773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17027
  · exact u17028

def r33774 : Route 9 := (fun mask => (mask,id))

def c33774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33774 : Upper (D 6) (R 6) [10,160,18,65,260] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,260] 13 (by decide) (choices 1) [1,4,64] r33774 c33774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17029
  · exact u17030
  · exact u17031

def r33775 : Route 9 := (fun mask => (mask,id))

def c33775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33775 : Upper (D 6) (R 6) [10,160,18,65,288] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,288] 13 (by decide) (choices 1) [1,4,64] r33775 c33775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17032
  · exact u17033
  · exact u17034

def r33776 : Route 9 := (fun mask => (mask,id))

def c33776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33776 : Upper (D 6) (R 6) [10,160,18,65,320] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,320] 13 (by decide) (choices 1) [1,4] r33776 c33776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17035
  · exact u17036

def b33777 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 22 76 81 293 357 421 293), lower := (rows 11 162 22 76 81 32 64 128 256), losses := [] }

theorem u33777 : Upper (D 6) (R 6) [10,160,18,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33778 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 329, targets := 32 },{ cop := 3, region := 419, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 22 76 112 293 325 389 261), lower := (rows 11 162 22 76 112 32 64 128 256), losses := [] }

theorem u33778 : Upper (D 6) (R 6) [10,160,18,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33779 : Route 9 := (fun mask => (mask,id))

def c33779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33779 : Upper (D 6) (R 6) [10,160,18,68,257] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,257] 13 (by decide) (choices 1) [1,4,64] r33779 c33779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17037
  · exact u17038
  · exact u17039

#print axioms u33779
end Delivery.IrregularNine14.P06
