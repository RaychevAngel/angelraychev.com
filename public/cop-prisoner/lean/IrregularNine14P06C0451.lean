import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0141
import IrregularNine14P06C0142

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27060 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 324 73 22 34 101 165 293), lower := (rows 41 146 324 73 22 34 64 128 256), losses := [] }

theorem u27060 : Upper (D 6) (R 6) [40,144,320,65,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27061 : Route 9 := (fun mask => (mask,id))

def c27061 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27061 : Upper (D 6) (R 6) [40,144,320,65,6,4] 13 := by
  apply FastRouting.sound _ _ [40,144,320,65,6,4] 13 (by decide) (choices 1) [1,2,32] r27061 c27061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8500
  · exact u8501
  · exact u8502

def b27062 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 146 324 73 50 33 70 134 262), lower := (rows 41 146 324 73 50 33 64 128 256), losses := [] }

theorem u27062 : Upper (D 6) (R 6) [40,144,320,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27063 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 50, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 146 324 73 50 34 69 133 261), lower := (rows 41 146 324 73 50 34 64 128 256), losses := [] }

theorem u27063 : Upper (D 6) (R 6) [40,144,320,65,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27064 : Route 9 := (fun mask => (mask,id))

def c27064 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27064 : Upper (D 6) (R 6) [40,144,320,65,34,4] 13 := by
  apply FastRouting.sound _ _ [40,144,320,65,34,4] 13 (by decide) (choices 1) [1,2,4] r27064 c27064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8503
  · exact u8504
  · exact u8505

def b27065 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 146 324 73 52 33 70 134 262), lower := (rows 41 146 324 73 52 33 64 128 256), losses := [] }

theorem u27065 : Upper (D 6) (R 6) [40,144,320,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27066 : Route 9 := (fun mask => (mask,id))

def c27066 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27066 : Upper (D 6) (R 6) [40,144,320,65,36,2] 13 := by
  apply FastRouting.sound _ _ [40,144,320,65,36,2] 13 (by decide) (choices 1) [1,2,4] r27066 c27066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8506
  · exact u8507
  · exact u8508

def b27067 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 146 324 73 52 36 67 131 259), lower := (rows 41 146 324 73 52 36 64 128 256), losses := [] }

theorem u27067 : Upper (D 6) (R 6) [40,144,320,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27068 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 146 324 74 19 33 100 164 292), lower := (rows 41 146 324 74 19 33 64 128 256), losses := [] }

theorem u27068 : Upper (D 6) (R 6) [40,144,320,66,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27069 : Route 9 := (fun mask => (mask,id))

def c27069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27069 : Upper (D 6) (R 6) [40,144,320,66,3,4] 13 := by
  apply FastRouting.sound _ _ [40,144,320,66,3,4] 13 (by decide) (choices 1) [1,4,32] r27069 c27069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8509
  · exact u8510
  · exact u8511

def b27070 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 146 324 74 21 33 102 166 294), lower := (rows 41 146 324 74 21 33 64 128 256), losses := [] }

theorem u27070 : Upper (D 6) (R 6) [40,144,320,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27071 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 146 324 74 21 34 101 165 293), lower := (rows 41 146 324 74 21 34 64 128 256), losses := [] }

theorem u27071 : Upper (D 6) (R 6) [40,144,320,66,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27072 : Route 9 := (fun mask => (mask,id))

def c27072 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27072 : Upper (D 6) (R 6) [40,144,320,66,5,4] 13 := by
  apply FastRouting.sound _ _ [40,144,320,66,5,4] 13 (by decide) (choices 1) [1,2,32] r27072 c27072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8512
  · exact u8513
  · exact u8514

def b27073 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 293, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 41 146 324 74 22 33 101 165 293), lower := (rows 41 146 324 74 22 33 64 128 256), losses := [] }

theorem u27073 : Upper (D 6) (R 6) [40,144,320,66,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27074 : Route 9 := (fun mask => (mask,id))

def c27074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27074 : Upper (D 6) (R 6) [40,144,320,66,6,4] 13 := by
  apply FastRouting.sound _ _ [40,144,320,66,6,4] 13 (by decide) (choices 1) [1,32] r27074 c27074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8515
  · exact u8516

def b27075 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 146 324 74 52 33 71 135 263), lower := (rows 41 146 324 74 52 33 64 128 256), losses := [] }

theorem u27075 : Upper (D 6) (R 6) [40,144,320,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27076 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 146 324 74 52 34 69 133 261), lower := (rows 41 146 324 74 52 34 64 128 256), losses := [] }

theorem u27076 : Upper (D 6) (R 6) [40,144,320,66,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27077 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 146 324 74 52 36 67 131 259), lower := (rows 41 146 324 74 52 36 64 128 256), losses := [] }

theorem u27077 : Upper (D 6) (R 6) [40,144,320,66,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27078 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 340, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 162 324 13 22 33 82 210 338), lower := (rows 41 162 324 13 22 33 64 128 256), losses := [] }

theorem u27078 : Upper (D 6) (R 6) [40,160,320,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27079 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 162 324 13 22 34 81 209 337), lower := (rows 41 162 324 13 22 34 64 128 256), losses := [] }

theorem u27079 : Upper (D 6) (R 6) [40,160,320,5,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27080 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 162 324 13 22 48 67 195 323), lower := (rows 41 162 324 13 22 48 64 128 256), losses := [] }

theorem u27080 : Upper (D 6) (R 6) [40,160,320,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27080 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27081 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 41, targets := 2 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 162 324 13 22 96 83 147 275), lower := (rows 41 162 324 13 22 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 100 64 128 256), good := (rows 41 162 352 41 50 96 96 128 256) }] }

theorem u27081 : Upper (D 6) (R 6) [40,160,320,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27082 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 162 324 13 81 34 86 150 278), lower := (rows 41 162 324 13 81 34 64 128 256), losses := [] }

theorem u27082 : Upper (D 6) (R 6) [40,160,320,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27083 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 162 324 13 81 36 82 146 274), lower := (rows 41 162 324 13 81 36 64 128 256), losses := [] }

theorem u27083 : Upper (D 6) (R 6) [40,160,320,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27084 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 41 162 324 13 81 48 70 134 262), lower := (rows 41 162 324 13 81 48 64 128 256), losses := [] }

theorem u27084 : Upper (D 6) (R 6) [40,160,320,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27084 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27085 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 340, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 162 324 13 82 33 86 150 278), lower := (rows 41 162 324 13 82 33 64 128 256), losses := [] }

theorem u27085 : Upper (D 6) (R 6) [40,160,320,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27086 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 162 324 13 82 34 85 149 277), lower := (rows 41 162 324 13 82 34 64 128 256), losses := [] }

theorem u27086 : Upper (D 6) (R 6) [40,160,320,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27087 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 162 324 13 82 36 83 147 275), lower := (rows 41 162 324 13 82 36 64 128 256), losses := [] }

theorem u27087 : Upper (D 6) (R 6) [40,160,320,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27088 : Route 9 := (fun mask => (mask,id))

def c27088 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27088 : Upper (D 6) (R 6) [40,160,320,5,66,16] 13 := by
  apply FastRouting.sound _ _ [40,160,320,5,66,16] 13 (by decide) (choices 1) [1,2,4] r27088 c27088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8517
  · exact u8518
  · exact u8519

def b27089 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 162 324 14 21 33 82 210 338), lower := (rows 41 162 324 14 21 33 64 128 256), losses := [] }

theorem u27089 : Upper (D 6) (R 6) [40,160,320,6,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27090 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 162 324 14 21 34 81 209 337), lower := (rows 41 162 324 14 21 34 64 128 256), losses := [] }

theorem u27090 : Upper (D 6) (R 6) [40,160,320,6,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27091 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 162 324 14 21 48 67 195 323), lower := (rows 41 162 324 14 21 48 64 128 256), losses := [] }

theorem u27091 : Upper (D 6) (R 6) [40,160,320,6,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27091 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27092 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(0,1),(1,2),(4,1)], upper := (rows 41 162 324 14 21 96 83 147 275), lower := (rows 41 162 324 14 21 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 100 64 128 256), good := (rows 57 160 356 61 53 96 96 128 256) }] }

theorem u27092 : Upper (D 6) (R 6) [40,160,320,6,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27093 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 162 324 14 81 33 86 150 278), lower := (rows 41 162 324 14 81 33 64 128 256), losses := [] }

theorem u27093 : Upper (D 6) (R 6) [40,160,320,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27094 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 162 324 14 81 34 85 149 277), lower := (rows 41 162 324 14 81 34 64 128 256), losses := [] }

theorem u27094 : Upper (D 6) (R 6) [40,160,320,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27095 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 162 324 14 81 36 83 147 275), lower := (rows 41 162 324 14 81 36 64 128 256), losses := [] }

theorem u27095 : Upper (D 6) (R 6) [40,160,320,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27096 : Route 9 := (fun mask => (mask,id))

def c27096 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27096 : Upper (D 6) (R 6) [40,160,320,6,65,16] 13 := by
  apply FastRouting.sound _ _ [40,160,320,6,65,16] 13 (by decide) (choices 1) [1,2,4] r27096 c27096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8520
  · exact u8521
  · exact u8522

def b27097 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 162 324 14 82 33 85 149 277), lower := (rows 41 162 324 14 82 33 64 128 256), losses := [] }

theorem u27097 : Upper (D 6) (R 6) [40,160,320,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27098 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 162 324 14 82 36 81 145 273), lower := (rows 41 162 324 14 82 36 64 128 256), losses := [] }

theorem u27098 : Upper (D 6) (R 6) [40,160,320,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27099 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 324, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 41 162 324 14 82 48 69 133 261), lower := (rows 41 162 324 14 82 48 64 128 256), losses := [] }

theorem u27099 : Upper (D 6) (R 6) [40,160,320,6,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27099 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27100 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 162 324 25 22 33 70 198 326), lower := (rows 41 162 324 25 22 33 64 128 256), losses := [] }

theorem u27100 : Upper (D 6) (R 6) [40,160,320,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27101 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 162 324 25 22 34 69 197 325), lower := (rows 41 162 324 25 22 34 64 128 256), losses := [] }

theorem u27101 : Upper (D 6) (R 6) [40,160,320,17,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27102 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 162 324 25 22 36 67 195 323), lower := (rows 41 162 324 25 22 36 64 128 256), losses := [] }

theorem u27102 : Upper (D 6) (R 6) [40,160,320,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27103 : PairBound 9 := { available := 7, camps := [], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 162 324 25 22 96 71 135 263), lower := (rows 41 162 324 25 22 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 24 16 100 64 128 256), good := (rows 41 160 356 25 61 96 96 128 256) },{ target := 2, region := (rows 17 2 0 24 16 100 64 128 256), good := (rows 41 162 352 25 59 96 96 128 256) }] }

theorem u27103 : Upper (D 6) (R 6) [40,160,320,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27104 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 162 324 25 82 33 70 134 262), lower := (rows 41 162 324 25 82 33 64 128 256), losses := [] }

theorem u27104 : Upper (D 6) (R 6) [40,160,320,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27105 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 162 324 25 82 34 69 133 261), lower := (rows 41 162 324 25 82 34 64 128 256), losses := [] }

theorem u27105 : Upper (D 6) (R 6) [40,160,320,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27106 : Route 9 := (fun mask => (mask,id))

def c27106 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27106 : Upper (D 6) (R 6) [40,160,320,17,66,4] 13 := by
  apply FastRouting.sound _ _ [40,160,320,17,66,4] 13 (by decide) (choices 1) [1,2,4] r27106 c27106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8523
  · exact u8524
  · exact u8525

def b27107 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 162 324 26 21 33 70 198 326), lower := (rows 41 162 324 26 21 33 64 128 256), losses := [] }

theorem u27107 : Upper (D 6) (R 6) [40,160,320,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27108 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 162 324 26 21 34 69 197 325), lower := (rows 41 162 324 26 21 34 64 128 256), losses := [] }

theorem u27108 : Upper (D 6) (R 6) [40,160,320,18,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27109 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 194, targets := 4 }], pairs := [(0,1),(1,2),(3,2)], upper := (rows 41 162 324 26 21 36 67 195 323), lower := (rows 41 162 324 26 21 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 160 356 57 53 36 64 128 256) },{ target := 2, region := (rows 1 3 0 24 16 32 81 145 273), good := (rows 491 162 320 474 475 32 64 128 256) }] }

theorem u27109 : Upper (D 6) (R 6) [40,160,320,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27110 : Route 9 := (fun mask => (mask,id))

def c27110 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27110 : Upper (D 6) (R 6) [40,160,320,18,5,64] 13 := by
  apply FastRouting.sound _ _ [40,160,320,18,5,64] 13 (by decide) (choices 1) [1,2,4] r27110 c27110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8526
  · exact u8527
  · exact u8528

def b27111 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 162 324 26 81 33 70 134 262), lower := (rows 41 162 324 26 81 33 64 128 256), losses := [] }

theorem u27111 : Upper (D 6) (R 6) [40,160,320,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27112 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 162 324 26 81 34 69 133 261), lower := (rows 41 162 324 26 81 34 64 128 256), losses := [] }

theorem u27112 : Upper (D 6) (R 6) [40,160,320,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27113 : Route 9 := (fun mask => (mask,id))

def c27113 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27113 : Upper (D 6) (R 6) [40,160,320,18,65,4] 13 := by
  apply FastRouting.sound _ _ [40,160,320,18,65,4] 13 (by decide) (choices 1) [1,2,4] r27113 c27113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8529
  · exact u8530
  · exact u8531

def b27114 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 332, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 162 324 28 19 33 70 198 326), lower := (rows 41 162 324 28 19 33 64 128 256), losses := [] }

theorem u27114 : Upper (D 6) (R 6) [40,160,320,20,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27115 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 162 324 28 19 34 69 197 325), lower := (rows 41 162 324 28 19 34 64 128 256), losses := [] }

theorem u27115 : Upper (D 6) (R 6) [40,160,320,20,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27116 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 162 324 28 19 36 67 195 323), lower := (rows 41 162 324 28 19 36 64 128 256), losses := [] }

theorem u27116 : Upper (D 6) (R 6) [40,160,320,20,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27117 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 332, targets := 32 }], pairs := [(0,1),(2,5),(3,5)], upper := (rows 41 162 324 28 19 96 71 135 263), lower := (rows 41 162 324 28 19 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 100 64 128 256), good := (rows 41 160 356 61 17 96 96 128 256) }] }

theorem u27117 : Upper (D 6) (R 6) [40,160,320,20,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27118 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 162 324 28 81 33 70 134 262), lower := (rows 41 162 324 28 81 33 64 128 256), losses := [] }

theorem u27118 : Upper (D 6) (R 6) [40,160,320,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27119 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 162 324 28 81 34 71 135 263), lower := (rows 41 162 324 28 81 34 64 128 256), losses := [] }

theorem u27119 : Upper (D 6) (R 6) [40,160,320,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27119
end Delivery.IrregularNine14.P06
