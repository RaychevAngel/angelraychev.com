import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0263
import IrregularNine14P06C0264

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33000 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 41 22 116 84 212 340), lower := (rows 11 131 292 41 22 32 64 128 256), losses := [] }

theorem u33000 : Upper (D 6) (R 6) [10,129,288,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33001 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 41 82 116 84 212 340), lower := (rows 11 131 292 41 82 32 64 128 256), losses := [] }

theorem u33001 : Upper (D 6) (R 6) [10,129,288,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33002 : Route 9 := (fun mask => (mask,id))

def c33002 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33002 : Upper (D 6) (R 6) [10,129,288,33,68] 13 := by
  apply FastRouting.sound _ _ [10,129,288,33,68] 13 (by decide) (choices 1) [2,4,16,64] r33002 c33002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15793
  · exact u15794
  · exact u15795
  · exact u15796

def b33003 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 56 19 100 68 196 324), lower := (rows 11 131 292 56 19 32 64 128 256), losses := [] }

theorem u33003 : Upper (D 6) (R 6) [10,129,288,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33004 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 356, targets := 1 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 11 131 292 56 21 102 70 198 326), lower := (rows 11 131 292 56 21 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 494 486 292 60 508 32 64 128 256) }] }

theorem u33004 : Upper (D 6) (R 6) [10,129,288,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33005 : Route 9 := (fun mask => (mask,id))

def c33005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33005 : Upper (D 6) (R 6) [10,129,288,48,6] 13 := by
  apply FastRouting.sound _ _ [10,129,288,48,6] 13 (by decide) (choices 1) [1,4,64] r33005 c33005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15797
  · exact u15798
  · exact u15799

def r33006 : Route 9 := (fun mask => (mask,id))

def c33006 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33006 : Upper (D 6) (R 6) [10,129,288,48,65] 13 := by
  apply FastRouting.sound _ _ [10,129,288,48,65] 13 (by decide) (choices 1) [2,4,64] r33006 c33006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15800
  · exact u15801
  · exact u15802

def r33007 : Route 9 := (fun mask => (mask,id))

def c33007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33007 : Upper (D 6) (R 6) [10,129,288,48,66] 13 := by
  apply FastRouting.sound _ _ [10,129,288,48,66] 13 (by decide) (choices 1) [1,4,64] r33007 c33007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15803
  · exact u15804
  · exact u15805

def r33008 : Route 9 := (fun mask => (mask,id))

def c33008 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33008 : Upper (D 6) (R 6) [10,129,288,48,68] 13 := by
  apply FastRouting.sound _ _ [10,129,288,48,68] 13 (by decide) (choices 1) [1,2,4,64] r33008 c33008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15806
  · exact u15807
  · exact u15808
  · exact u15809

def b33009 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 73 22 116 116 244 372), lower := (rows 11 131 292 73 22 32 64 128 256), losses := [] }

theorem u33009 : Upper (D 6) (R 6) [10,129,288,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33010 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 73 50 116 84 212 340), lower := (rows 11 131 292 73 50 32 64 128 256), losses := [] }

theorem u33010 : Upper (D 6) (R 6) [10,129,288,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33011 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 292 73 52 118 86 214 342), lower := (rows 11 131 292 73 52 32 64 128 256), losses := [] }

theorem u33011 : Upper (D 6) (R 6) [10,129,288,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33012 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 131 292 73 82 52 116 180 308), lower := (rows 11 131 292 73 82 32 64 128 256), losses := [] }

theorem u33012 : Upper (D 6) (R 6) [10,129,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33013 : Route 9 := (fun mask => (mask,id))

def c33013 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33013 : Upper (D 6) (R 6) [10,129,288,65,68] 13 := by
  apply FastRouting.sound _ _ [10,129,288,65,68] 13 (by decide) (choices 1) [2,4,16] r33013 c33013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15810
  · exact u15811
  · exact u15812

def r33014 : Route 9 := (fun mask => (mask,id))

def c33014 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33014 : Upper (D 6) (R 6) [10,129,288,65,96] 13 := by
  apply FastRouting.sound _ _ [10,129,288,65,96] 13 (by decide) (choices 1) [2,4,16] r33014 c33014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15813
  · exact u15814
  · exact u15815

def b33015 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 76 19 116 116 244 372), lower := (rows 11 131 292 76 19 32 64 128 256), losses := [] }

theorem u33015 : Upper (D 6) (R 6) [10,129,288,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33016 : Route 9 := (fun mask => (mask,id))

def c33016 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33016 : Upper (D 6) (R 6) [10,129,288,68,5] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,5] 13 (by decide) (choices 1) [2,16,64] r33016 c33016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15816
  · exact u15817
  · exact u15818

def r33017 : Route 9 := (fun mask => (mask,id))

def c33017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33017 : Upper (D 6) (R 6) [10,129,288,68,6] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,6] 13 (by decide) (choices 1) [1,16,64] r33017 c33017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15819
  · exact u15820
  · exact u15821

def r33018 : Route 9 := (fun mask => (mask,id))

def c33018 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33018 : Upper (D 6) (R 6) [10,129,288,68,33] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,33] 13 (by decide) (choices 1) [2,4,16,64] r33018 c33018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15822
  · exact u15823
  · exact u15824
  · exact u15825

def r33019 : Route 9 := (fun mask => (mask,id))

def c33019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33019 : Upper (D 6) (R 6) [10,129,288,68,34] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,34] 13 (by decide) (choices 1) [1,4,16,64] r33019 c33019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15826
  · exact u15827
  · exact u15828
  · exact u15829

def b33020 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 292 76 52 115 83 211 339), lower := (rows 11 131 292 76 52 32 64 128 256), losses := [] }

theorem u33020 : Upper (D 6) (R 6) [10,129,288,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33021 : Route 9 := (fun mask => (mask,id))

def c33021 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33021 : Upper (D 6) (R 6) [10,129,288,68,65] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,65] 13 (by decide) (choices 1) [2,4,16] r33021 c33021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15830
  · exact u15831
  · exact u15832

def r33022 : Route 9 := (fun mask => (mask,id))

def c33022 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33022 : Upper (D 6) (R 6) [10,129,288,68,66] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,66] 13 (by decide) (choices 1) [1,4,16] r33022 c33022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15833
  · exact u15834
  · exact u15835

def b33023 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 131 292 76 84 51 115 179 307), lower := (rows 11 131 292 76 84 32 64 128 256), losses := [] }

theorem u33023 : Upper (D 6) (R 6) [10,129,288,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33024 : Route 9 := (fun mask => (mask,id))

def c33024 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33024 : Upper (D 6) (R 6) [10,129,288,68,96] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68,96] 13 (by decide) (choices 1) [1,2,4,16] r33024 c33024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15836
  · exact u15837
  · exact u15838
  · exact u15839

def b33025 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 88 19 100 100 228 356), lower := (rows 11 131 292 88 19 32 64 128 256), losses := [] }

theorem u33025 : Upper (D 6) (R 6) [10,129,288,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33026 : Route 9 := (fun mask => (mask,id))

def c33026 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33026 : Upper (D 6) (R 6) [10,129,288,80,5] 13 := by
  apply FastRouting.sound _ _ [10,129,288,80,5] 13 (by decide) (choices 1) [2,4,64] r33026 c33026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15840
  · exact u15841
  · exact u15842

def r33027 : Route 9 := (fun mask => (mask,id))

def c33027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33027 : Upper (D 6) (R 6) [10,129,288,80,6] 13 := by
  apply FastRouting.sound _ _ [10,129,288,80,6] 13 (by decide) (choices 1) [1,4,64] r33027 c33027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15843
  · exact u15844
  · exact u15845

def r33028 : Route 9 := (fun mask => (mask,id))

def c33028 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33028 : Upper (D 6) (R 6) [10,129,288,80,33] 13 := by
  apply FastRouting.sound _ _ [10,129,288,80,33] 13 (by decide) (choices 1) [2,4,64] r33028 c33028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15846
  · exact u15847
  · exact u15848

def r33029 : Route 9 := (fun mask => (mask,id))

def c33029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33029 : Upper (D 6) (R 6) [10,129,288,80,34] 13 := by
  apply FastRouting.sound _ _ [10,129,288,80,34] 13 (by decide) (choices 1) [1,4,64] r33029 c33029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15849
  · exact u15850
  · exact u15851

def b33030 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 292 88 52 103 71 199 327), lower := (rows 11 131 292 88 52 32 64 128 256), losses := [] }

theorem u33030 : Upper (D 6) (R 6) [10,129,288,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33031 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 292 88 81 38 102 166 294), lower := (rows 11 131 292 88 81 32 64 128 256), losses := [] }

theorem u33031 : Upper (D 6) (R 6) [10,129,288,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33032 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 131 292 88 82 37 101 165 293), lower := (rows 11 131 292 88 82 32 64 128 256), losses := [] }

theorem u33032 : Upper (D 6) (R 6) [10,129,288,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33033 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 292 88 84 39 103 167 295), lower := (rows 11 131 292 88 84 32 64 128 256), losses := [] }

theorem u33033 : Upper (D 6) (R 6) [10,129,288,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33034 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 292 88 112 39 71 135 263), lower := (rows 11 131 292 88 112 32 64 128 256), losses := [] }

theorem u33034 : Upper (D 6) (R 6) [10,129,288,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33035 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 104 19 116 84 212 340), lower := (rows 11 131 292 104 19 32 64 128 256), losses := [] }

theorem u33035 : Upper (D 6) (R 6) [10,129,288,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33036 : Route 9 := (fun mask => (mask,id))

def c33036 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33036 : Upper (D 6) (R 6) [10,129,288,96,5] 13 := by
  apply FastRouting.sound _ _ [10,129,288,96,5] 13 (by decide) (choices 1) [2,4,16,64] r33036 c33036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15852
  · exact u15853
  · exact u15854
  · exact u15855

def r33037 : Route 9 := (fun mask => (mask,id))

def c33037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33037 : Upper (D 6) (R 6) [10,129,288,96,6] 13 := by
  apply FastRouting.sound _ _ [10,129,288,96,6] 13 (by decide) (choices 1) [1,4,16,64] r33037 c33037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15856
  · exact u15857
  · exact u15858
  · exact u15859

def r33038 : Route 9 := (fun mask => (mask,id))

def c33038 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33038 : Upper (D 6) (R 6) [10,129,288,96,65] 13 := by
  apply FastRouting.sound _ _ [10,129,288,96,65] 13 (by decide) (choices 1) [2,4,16] r33038 c33038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15860
  · exact u15861
  · exact u15862

def r33039 : Route 9 := (fun mask => (mask,id))

def c33039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33039 : Upper (D 6) (R 6) [10,129,288,96,66] 13 := by
  apply FastRouting.sound _ _ [10,129,288,96,66] 13 (by decide) (choices 1) [1,4,16] r33039 c33039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15863
  · exact u15864
  · exact u15865

def r33040 : Route 9 := (fun mask => (mask,id))

def c33040 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33040 : Upper (D 6) (R 6) [10,129,288,96,68] 13 := by
  apply FastRouting.sound _ _ [10,129,288,96,68] 13 (by decide) (choices 1) [1,2,4,16] r33040 c33040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15866
  · exact u15867
  · exact u15868
  · exact u15869

def b33041 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 37 25 22 352 352 480 352), lower := (rows 11 134 37 25 22 32 64 128 256), losses := [] }

theorem u33041 : Upper (D 6) (R 6) [10,132,33,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33042 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 37 25 50 356 324 452 324), lower := (rows 11 134 37 25 50 32 64 128 256), losses := [] }

theorem u33042 : Upper (D 6) (R 6) [10,132,33,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33043 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 24, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 11 134 37 25 52 354 322 450 322), lower := (rows 11 134 37 25 52 32 64 128 256), losses := [] }

theorem u33043 : Upper (D 6) (R 6) [10,132,33,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33044 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 37 25 82 356 356 484 356), lower := (rows 11 134 37 25 82 32 64 128 256), losses := [] }

theorem u33044 : Upper (D 6) (R 6) [10,132,33,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33045 : Route 9 := (fun mask => (mask,id))

def c33045 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33045 : Upper (D 6) (R 6) [10,132,33,17,68] 13 := by
  apply FastRouting.sound _ _ [10,132,33,17,68] 13 (by decide) (choices 1) [2,64,256] r33045 c33045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15870
  · exact u15871
  · exact u15872

def b33046 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 134 37 25 112 358 326 454 326), lower := (rows 11 134 37 25 112 32 64 128 256), losses := [] }

theorem u33046 : Upper (D 6) (R 6) [10,132,33,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33047 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 37 25 274 100 100 228 356), lower := (rows 11 134 37 25 274 32 64 128 256), losses := [] }

theorem u33047 : Upper (D 6) (R 6) [10,132,33,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33048 : Route 9 := (fun mask => (mask,id))

def c33048 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33048 : Upper (D 6) (R 6) [10,132,33,17,260] 13 := by
  apply FastRouting.sound _ _ [10,132,33,17,260] 13 (by decide) (choices 1) [2,64] r33048 c33048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15873
  · exact u15874

def b33049 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 134 37 25 304 102 70 198 326), lower := (rows 11 134 37 25 304 32 64 128 256), losses := [] }

theorem u33049 : Upper (D 6) (R 6) [10,132,33,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33050 : Route 9 := (fun mask => (mask,id))

def c33050 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33050 : Upper (D 6) (R 6) [10,132,33,17,320] 13 := by
  apply FastRouting.sound _ _ [10,132,33,17,320] 13 (by decide) (choices 1) [2,4,64] r33050 c33050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15875
  · exact u15876
  · exact u15877

def b33051 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 37 28 19 352 352 480 352), lower := (rows 11 134 37 28 19 32 64 128 256), losses := [] }

theorem u33051 : Upper (D 6) (R 6) [10,132,33,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33052 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 24, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 11 134 37 28 49 354 322 450 322), lower := (rows 11 134 37 28 49 32 64 128 256), losses := [] }

theorem u33052 : Upper (D 6) (R 6) [10,132,33,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33053 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 13, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 134 37 28 50 353 321 449 321), lower := (rows 11 134 37 28 50 32 64 128 256), losses := [] }

theorem u33053 : Upper (D 6) (R 6) [10,132,33,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33054 : Route 9 := (fun mask => (mask,id))

def c33054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33054 : Upper (D 6) (R 6) [10,132,33,20,65] 13 := by
  apply FastRouting.sound _ _ [10,132,33,20,65] 13 (by decide) (choices 1) [2,64,256] r33054 c33054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15878
  · exact u15879
  · exact u15880

def r33055 : Route 9 := (fun mask => (mask,id))

def c33055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33055 : Upper (D 6) (R 6) [10,132,33,20,66] 13 := by
  apply FastRouting.sound _ _ [10,132,33,20,66] 13 (by decide) (choices 1) [1,64,256] r33055 c33055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15881
  · exact u15882
  · exact u15883

def b33056 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 451, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 11 134 37 28 112 355 323 451 323), lower := (rows 11 134 37 28 112 32 64 128 256), losses := [] }

theorem u33056 : Upper (D 6) (R 6) [10,132,33,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33057 : Route 9 := (fun mask => (mask,id))

def c33057 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33057 : Upper (D 6) (R 6) [10,132,33,20,257] 13 := by
  apply FastRouting.sound _ _ [10,132,33,20,257] 13 (by decide) (choices 1) [2,64] r33057 c33057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15884
  · exact u15885

def r33058 : Route 9 := (fun mask => (mask,id))

def c33058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33058 : Upper (D 6) (R 6) [10,132,33,20,258] 13 := by
  apply FastRouting.sound _ _ [10,132,33,20,258] 13 (by decide) (choices 1) [1,64] r33058 c33058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15886
  · exact u15887

def b33059 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 11 134 37 28 304 99 67 195 323), lower := (rows 11 134 37 28 304 32 64 128 256), losses := [] }

theorem u33059 : Upper (D 6) (R 6) [10,132,33,20,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u33059
end Delivery.IrregularNine14.P06
