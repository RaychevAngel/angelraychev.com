import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0312
import IrregularNine14P06C0313
import IrregularNine14P06C0314

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35100 : Route 9 := (fun mask => (mask,id))

def c35100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35100 : Upper (D 6) (R 6) [24,36,130,33,66] 13 := by
  apply FastRouting.sound _ _ [24,36,130,33,66] 13 (by decide) (choices 1) [1,4,64,256] r35100 c35100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18771
  · exact u18772
  · exact u18773
  · exact u18774

def r35101 : Route 9 := (fun mask => (mask,id))

def c35101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35101 : Upper (D 6) (R 6) [24,36,130,33,68] 13 := by
  apply FastRouting.sound _ _ [24,36,130,33,68] 13 (by decide) (choices 1) [1,2,64,256] r35101 c35101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18775
  · exact u18776
  · exact u18777
  · exact u18778

def b35102 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 38 134 41 273 102 70 198 326), lower := (rows 25 38 134 41 273 32 64 128 256), losses := [] }

theorem u35102 : Upper (D 6) (R 6) [24,36,130,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35103 : Route 9 := (fun mask => (mask,id))

def c35103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35103 : Upper (D 6) (R 6) [24,36,130,33,258] 13 := by
  apply FastRouting.sound _ _ [24,36,130,33,258] 13 (by decide) (choices 1) [1,4,64] r35103 c35103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18779
  · exact u18780
  · exact u18781

def r35104 : Route 9 := (fun mask => (mask,id))

def c35104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35104 : Upper (D 6) (R 6) [24,36,130,33,260] 13 := by
  apply FastRouting.sound _ _ [24,36,130,33,260] 13 (by decide) (choices 1) [1,2,64] r35104 c35104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18782
  · exact u18783
  · exact u18784

def r35105 : Route 9 := (fun mask => (mask,id))

def c35105 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35105 : Upper (D 6) (R 6) [24,36,130,33,320] 13 := by
  apply FastRouting.sound _ _ [24,36,130,33,320] 13 (by decide) (choices 1) [1,2,4,64] r35105 c35105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18785
  · exact u18786
  · exact u18787
  · exact u18788

def b35106 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 134 42 81 357 325 453 325), lower := (rows 25 38 134 42 81 32 64 128 256), losses := [] }

theorem u35106 : Upper (D 6) (R 6) [24,36,130,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35107 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 134 42 84 353 321 449 321), lower := (rows 25 38 134 42 84 32 64 128 256), losses := [] }

theorem u35107 : Upper (D 6) (R 6) [24,36,130,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35108 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 134 42 273 101 69 197 325), lower := (rows 25 38 134 42 273 32 64 128 256), losses := [] }

theorem u35108 : Upper (D 6) (R 6) [24,36,130,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35109 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 134 42 276 97 65 193 321), lower := (rows 25 38 134 42 276 32 64 128 256), losses := [] }

theorem u35109 : Upper (D 6) (R 6) [24,36,130,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35110 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 134 42 336 101 69 197 325), lower := (rows 25 38 134 42 336 32 64 128 256), losses := [] }

theorem u35110 : Upper (D 6) (R 6) [24,36,130,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35111 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 134 44 81 355 323 451 323), lower := (rows 25 38 134 44 81 32 64 128 256), losses := [] }

theorem u35111 : Upper (D 6) (R 6) [24,36,130,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35112 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 134 44 82 353 321 449 321), lower := (rows 25 38 134 44 82 32 64 128 256), losses := [] }

theorem u35112 : Upper (D 6) (R 6) [24,36,130,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35113 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 134 44 273 99 67 195 323), lower := (rows 25 38 134 44 273 32 64 128 256), losses := [] }

theorem u35113 : Upper (D 6) (R 6) [24,36,130,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35114 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 134 44 274 97 65 193 321), lower := (rows 25 38 134 44 274 32 64 128 256), losses := [] }

theorem u35114 : Upper (D 6) (R 6) [24,36,130,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35115 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 134 44 336 99 67 195 323), lower := (rows 25 38 134 44 336 32 64 128 256), losses := [] }

theorem u35115 : Upper (D 6) (R 6) [24,36,130,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35116 : PairBound 9 := { available := 294, camps := [{ cop := 6, region := 25, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 134 73 81 294 358 422 294), lower := (rows 25 38 134 73 81 32 64 128 256), losses := [] }

theorem u35116 : Upper (D 6) (R 6) [24,36,130,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35117 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 134 73 82 293 357 421 293), lower := (rows 25 38 134 73 82 32 64 128 256), losses := [] }

theorem u35117 : Upper (D 6) (R 6) [24,36,130,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35118 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 134 73 84 291 355 419 291), lower := (rows 25 38 134 73 84 32 64 128 256), losses := [] }

theorem u35118 : Upper (D 6) (R 6) [24,36,130,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35119 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 134 73 112 295 327 391 263), lower := (rows 25 38 134 73 112 32 64 128 256), losses := [] }

theorem u35119 : Upper (D 6) (R 6) [24,36,130,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35120 : Route 9 := (fun mask => (mask,id))

def c35120 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35120 : Upper (D 6) (R 6) [24,36,130,65,257] 13 := by
  apply FastRouting.sound _ _ [24,36,130,65,257] 13 (by decide) (choices 1) [2,4,64] r35120 c35120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18789
  · exact u18790
  · exact u18791

def r35121 : Route 9 := (fun mask => (mask,id))

def c35121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35121 : Upper (D 6) (R 6) [24,36,130,65,258] 13 := by
  apply FastRouting.sound _ _ [24,36,130,65,258] 13 (by decide) (choices 1) [1,4,64] r35121 c35121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18792
  · exact u18793
  · exact u18794

def r35122 : Route 9 := (fun mask => (mask,id))

def c35122 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35122 : Upper (D 6) (R 6) [24,36,130,65,260] 13 := by
  apply FastRouting.sound _ _ [24,36,130,65,260] 13 (by decide) (choices 1) [1,2,64] r35122 c35122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18795
  · exact u18796
  · exact u18797

def r35123 : Route 9 := (fun mask => (mask,id))

def c35123 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35123 : Upper (D 6) (R 6) [24,36,130,65,288] 13 := by
  apply FastRouting.sound _ _ [24,36,130,65,288] 13 (by decide) (choices 1) [1,2,4,64] r35123 c35123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18798
  · exact u18799
  · exact u18800
  · exact u18801

def b35124 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 134 73 336 39 103 167 295), lower := (rows 25 38 134 73 336 32 64 128 256), losses := [] }

theorem u35124 : Upper (D 6) (R 6) [24,36,130,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35125 : Route 9 := (fun mask => (mask,id))

def c35125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35125 : Upper (D 6) (R 6) [24,36,130,66,68] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,68] 13 (by decide) (choices 1) [1,256] r35125 c35125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18802
  · exact u18803

def r35126 : Route 9 := (fun mask => (mask,id))

def c35126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35126 : Upper (D 6) (R 6) [24,36,130,66,96] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,96] 13 (by decide) (choices 1) [1,4,256] r35126 c35126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18804
  · exact u18805
  · exact u18806

def r35127 : Route 9 := (fun mask => (mask,id))

def c35127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35127 : Upper (D 6) (R 6) [24,36,130,66,257] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,257] 13 (by decide) (choices 1) [1,4,64] r35127 c35127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18807
  · exact u18808
  · exact u18809

def r35128 : Route 9 := (fun mask => (mask,id))

def c35128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35128 : Upper (D 6) (R 6) [24,36,130,66,260] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,260] 13 (by decide) (choices 1) [1,64] r35128 c35128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18810
  · exact u18811

def r35129 : Route 9 := (fun mask => (mask,id))

def c35129 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35129 : Upper (D 6) (R 6) [24,36,130,66,288] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,288] 13 (by decide) (choices 1) [1,4,64] r35129 c35129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18812
  · exact u18813
  · exact u18814

def r35130 : Route 9 := (fun mask => (mask,id))

def c35130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35130 : Upper (D 6) (R 6) [24,36,130,66,320] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,320] 13 (by decide) (choices 1) [1,4] r35130 c35130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18815
  · exact u18816

def r35131 : Route 9 := (fun mask => (mask,id))

def c35131 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35131 : Upper (D 6) (R 6) [24,36,130,68,96] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,96] 13 (by decide) (choices 1) [1,2,256] r35131 c35131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18817
  · exact u18818
  · exact u18819

def r35132 : Route 9 := (fun mask => (mask,id))

def c35132 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35132 : Upper (D 6) (R 6) [24,36,130,68,257] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,257] 13 (by decide) (choices 1) [1,2,64] r35132 c35132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18820
  · exact u18821
  · exact u18822

def r35133 : Route 9 := (fun mask => (mask,id))

def c35133 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35133 : Upper (D 6) (R 6) [24,36,130,68,258] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,258] 13 (by decide) (choices 1) [1,64] r35133 c35133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18823
  · exact u18824

def r35134 : Route 9 := (fun mask => (mask,id))

def c35134 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35134 : Upper (D 6) (R 6) [24,36,130,68,288] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,288] 13 (by decide) (choices 1) [1,2,64] r35134 c35134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18825
  · exact u18826
  · exact u18827

def r35135 : Route 9 := (fun mask => (mask,id))

def c35135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35135 : Upper (D 6) (R 6) [24,36,130,68,320] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,320] 13 (by decide) (choices 1) [1,2] r35135 c35135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18828
  · exact u18829

def r35136 : Route 9 := (fun mask => (mask,id))

def c35136 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35136 : Upper (D 6) (R 6) [24,36,130,96,257] 13 := by
  apply FastRouting.sound _ _ [24,36,130,96,257] 13 (by decide) (choices 1) [1,2,4,64] r35136 c35136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18830
  · exact u18831
  · exact u18832
  · exact u18833

def r35137 : Route 9 := (fun mask => (mask,id))

def c35137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35137 : Upper (D 6) (R 6) [24,36,130,96,258] 13 := by
  apply FastRouting.sound _ _ [24,36,130,96,258] 13 (by decide) (choices 1) [1,4,64] r35137 c35137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18834
  · exact u18835
  · exact u18836

def r35138 : Route 9 := (fun mask => (mask,id))

def c35138 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35138 : Upper (D 6) (R 6) [24,36,130,96,260] 13 := by
  apply FastRouting.sound _ _ [24,36,130,96,260] 13 (by decide) (choices 1) [1,2,64] r35138 c35138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18837
  · exact u18838
  · exact u18839

def r35139 : Route 9 := (fun mask => (mask,id))

def c35139 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35139 : Upper (D 6) (R 6) [24,36,130,96,320] 13 := by
  apply FastRouting.sound _ _ [24,36,130,96,320] 13 (by decide) (choices 1) [1,2,4] r35139 c35139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18840
  · exact u18841
  · exact u18842

def b35140 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 38 196 11 19 356 356 484 356), lower := (rows 25 38 196 11 19 32 64 128 256), losses := [] }

theorem u35140 : Upper (D 6) (R 6) [24,36,192,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35141 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 38 196 11 21 354 354 482 354), lower := (rows 25 38 196 11 21 32 64 128 256), losses := [] }

theorem u35141 : Upper (D 6) (R 6) [24,36,192,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35142 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 38 196 11 22 353 353 481 353), lower := (rows 25 38 196 11 22 32 64 128 256), losses := [] }

theorem u35142 : Upper (D 6) (R 6) [24,36,192,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35143 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 38 196 11 49 358 326 454 326), lower := (rows 25 38 196 11 49 32 64 128 256), losses := [] }

theorem u35143 : Upper (D 6) (R 6) [24,36,192,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35144 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 38 196 11 50 357 325 453 325), lower := (rows 25 38 196 11 50 32 64 128 256), losses := [] }

theorem u35144 : Upper (D 6) (R 6) [24,36,192,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35145 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 196 11 52 355 323 451 323), lower := (rows 25 38 196 11 52 32 64 128 256), losses := [] }

theorem u35145 : Upper (D 6) (R 6) [24,36,192,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35146 : PairBound 9 := { available := 294, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 2, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 196 11 81 294 358 422 294), lower := (rows 25 38 196 11 81 32 64 128 256), losses := [] }

theorem u35146 : Upper (D 6) (R 6) [24,36,192,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35147 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 38 196 11 82 293 357 421 293), lower := (rows 25 38 196 11 82 32 64 128 256), losses := [] }

theorem u35147 : Upper (D 6) (R 6) [24,36,192,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35148 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 38 196 11 84 291 355 419 291), lower := (rows 25 38 196 11 84 32 64 128 256), losses := [] }

theorem u35148 : Upper (D 6) (R 6) [24,36,192,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35149 : Route 9 := (fun mask => (mask,id))

def c35149 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35149 : Upper (D 6) (R 6) [24,36,192,3,96] 13 := by
  apply FastRouting.sound _ _ [24,36,192,3,96] 13 (by decide) (choices 1) [1,2,4,256] r35149 c35149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18843
  · exact u18844
  · exact u18845
  · exact u18846

def r35150 : Route 9 := (fun mask => (mask,id))

def c35150 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35150 : Upper (D 6) (R 6) [24,36,192,3,257] 13 := by
  apply FastRouting.sound _ _ [24,36,192,3,257] 13 (by decide) (choices 1) [2,4,64] r35150 c35150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18847
  · exact u18848
  · exact u18849

def b35151 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 38 196 11 274 101 101 229 357), lower := (rows 25 38 196 11 274 32 64 128 256), losses := [] }

theorem u35151 : Upper (D 6) (R 6) [24,36,192,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35152 : Route 9 := (fun mask => (mask,id))

def c35152 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35152 : Upper (D 6) (R 6) [24,36,192,3,260] 13 := by
  apply FastRouting.sound _ _ [24,36,192,3,260] 13 (by decide) (choices 1) [1,2,64] r35152 c35152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18850
  · exact u18851
  · exact u18852

def r35153 : Route 9 := (fun mask => (mask,id))

def c35153 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35153 : Upper (D 6) (R 6) [24,36,192,3,288] 13 := by
  apply FastRouting.sound _ _ [24,36,192,3,288] 13 (by decide) (choices 1) [1,2,4,64] r35153 c35153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18853
  · exact u18854
  · exact u18855
  · exact u18856

def r35154 : Route 9 := (fun mask => (mask,id))

def c35154 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35154 : Upper (D 6) (R 6) [24,36,192,3,320] 13 := by
  apply FastRouting.sound _ _ [24,36,192,3,320] 13 (by decide) (choices 1) [1,2,4] r35154 c35154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18857
  · exact u18858
  · exact u18859

def b35155 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 25, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 196 13 49 354 322 450 322), lower := (rows 25 38 196 13 49 32 64 128 256), losses := [] }

theorem u35155 : Upper (D 6) (R 6) [24,36,192,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35156 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 196 13 50 355 323 451 323), lower := (rows 25 38 196 13 50 32 64 128 256), losses := [] }

theorem u35156 : Upper (D 6) (R 6) [24,36,192,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35157 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 25, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 38 196 13 81 290 354 418 290), lower := (rows 25 38 196 13 81 32 64 128 256), losses := [] }

theorem u35157 : Upper (D 6) (R 6) [24,36,192,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35158 : Route 9 := (fun mask => (mask,id))

def c35158 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35158 : Upper (D 6) (R 6) [24,36,192,5,66] 13 := by
  apply FastRouting.sound _ _ [24,36,192,5,66] 13 (by decide) (choices 1) [1,2,256] r35158 c35158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18860
  · exact u18861
  · exact u18862

def r35159 : Route 9 := (fun mask => (mask,id))

def c35159 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35159 : Upper (D 6) (R 6) [24,36,192,5,96] 13 := by
  apply FastRouting.sound _ _ [24,36,192,5,96] 13 (by decide) (choices 1) [1,2,256] r35159 c35159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18863
  · exact u18864
  · exact u18865

#print axioms u35159
end Delivery.IrregularNine14.P06
