import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0164
import IrregularNine14P07C0165

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27060 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(1,7),(3,6),(4,7)], upper := (rows 37 290 76 138 81 160 83 147 275), lower := (rows 37 290 76 138 81 160 64 128 256), losses := [] }

theorem u27060 : Upper (D 7) (R 7) [36,288,72,130,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27061 : Route 9 := (fun mask => (mask,id))

def c27061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27061 : Upper (D 7) (R 7) [36,288,72,130,66,1] 13 := by
  apply FastRouting.sound _ _ [36,288,72,130,66,1] 13 (by decide) (choices 1) [1,16,128] r27061 c27061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9899
  · exact u9900
  · exact u9901

def r27062 : Route 9 := (fun mask => (mask,id))

def c27062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27062 : Upper (D 7) (R 7) [36,288,72,130,66,16] 13 := by
  apply FastRouting.sound _ _ [36,288,72,130,66,16] 13 (by decide) (choices 1) [1,128] r27062 c27062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9902
  · exact u9903

def b27063 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 290 76 138 82 160 81 145 273), lower := (rows 37 290 76 138 82 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 288 109 168 80 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 290 45 170 18 160 0 160 256) }] }

theorem u27063 : Upper (D 7) (R 7) [36,288,72,130,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27064 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 354, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 290 76 138 145 33 82 210 338), lower := (rows 37 290 76 138 145 33 64 128 256), losses := [] }

theorem u27064 : Upper (D 7) (R 7) [36,288,72,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27065 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 37 290 76 138 145 34 81 209 337), lower := (rows 37 290 76 138 145 34 64 128 256), losses := [] }

theorem u27065 : Upper (D 7) (R 7) [36,288,72,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27066 : Route 9 := (fun mask => (mask,id))

def c27066 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27066 : Upper (D 7) (R 7) [36,288,72,130,129,16] 13 := by
  apply FastRouting.sound _ _ [36,288,72,130,129,16] 13 (by decide) (choices 1) [1,2] r27066 c27066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9904
  · exact u9905

def b27067 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 76 138 145 96 83 147 275), lower := (rows 37 290 76 138 145 96 64 128 256), losses := [] }

theorem u27067 : Upper (D 7) (R 7) [36,288,72,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27068 : Route 9 := (fun mask => (mask,id))

def c27068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27068 : Upper (D 7) (R 7) [36,288,72,130,192,1] 13 := by
  apply FastRouting.sound _ _ [36,288,72,130,192,1] 13 (by decide) (choices 1) [1,2,16] r27068 c27068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9906
  · exact u9907
  · exact u9908

def b27069 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 37 290 76 138 208 34 81 145 273), lower := (rows 37 290 76 138 208 34 64 128 256), losses := [] }

theorem u27069 : Upper (D 7) (R 7) [36,288,72,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27070 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 37 290 76 138 208 48 67 131 259), lower := (rows 37 290 76 138 208 48 64 128 256), losses := [] }

theorem u27070 : Upper (D 7) (R 7) [36,288,72,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27070 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27071 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 204, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 290 76 152 19 33 194 194 450), lower := (rows 37 290 76 152 19 33 64 128 256), losses := [] }

theorem u27071 : Upper (D 7) (R 7) [36,288,72,144,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27072 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 204, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 290 76 152 19 34 193 193 449), lower := (rows 37 290 76 152 19 34 64 128 256), losses := [] }

theorem u27072 : Upper (D 7) (R 7) [36,288,72,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27073 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 76 152 19 96 195 131 387), lower := (rows 37 290 76 152 19 96 64 128 256), losses := [] }

theorem u27073 : Upper (D 7) (R 7) [36,288,72,144,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27074 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 204, targets := 32 }], pairs := [(1,7),(2,5),(3,5),(4,7)], upper := (rows 37 290 76 152 19 160 67 195 323), lower := (rows 37 290 76 152 19 160 64 128 256), losses := [] }

theorem u27074 : Upper (D 7) (R 7) [36,288,72,144,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27075 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 290 76 152 81 33 194 130 386), lower := (rows 37 290 76 152 81 33 64 128 256), losses := [] }

theorem u27075 : Upper (D 7) (R 7) [36,288,72,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27076 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 37 290 76 152 81 34 195 131 387), lower := (rows 37 290 76 152 81 34 64 128 256), losses := [] }

theorem u27076 : Upper (D 7) (R 7) [36,288,72,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27077 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(1,7),(4,7)], upper := (rows 37 290 76 152 81 160 67 131 259), lower := (rows 37 290 76 152 81 160 64 128 256), losses := [] }

theorem u27077 : Upper (D 7) (R 7) [36,288,72,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27078 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 290 76 152 82 33 195 131 387), lower := (rows 37 290 76 152 82 33 64 128 256), losses := [] }

theorem u27078 : Upper (D 7) (R 7) [36,288,72,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27079 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 37 290 76 152 82 34 193 129 385), lower := (rows 37 290 76 152 82 34 64 128 256), losses := [] }

theorem u27079 : Upper (D 7) (R 7) [36,288,72,144,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27080 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(1,7),(4,7)], upper := (rows 37 290 76 152 82 160 67 131 259), lower := (rows 37 290 76 152 82 160 64 128 256), losses := [] }

theorem u27080 : Upper (D 7) (R 7) [36,288,72,144,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27081 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 196 11 82 33 216 152 408), lower := (rows 37 290 196 11 82 33 64 128 256), losses := [] }

theorem u27081 : Upper (D 7) (R 7) [36,288,192,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27082 : Route 9 := (fun mask => (mask,id))

def c27082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27082 : Upper (D 7) (R 7) [36,288,192,3,66,8] 13 := by
  apply FastRouting.sound _ _ [36,288,192,3,66,8] 13 (by decide) (choices 1) [1,16,128] r27082 c27082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9909
  · exact u9910
  · exact u9911

def b27083 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 3, region := 196, targets := 32 }], pairs := [(1,6),(2,5),(3,6)], upper := (rows 37 290 196 11 82 48 201 137 393), lower := (rows 37 290 196 11 82 48 64 128 256), losses := [] }

theorem u27083 : Upper (D 7) (R 7) [36,288,192,3,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27083 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27084 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 290 196 11 82 160 89 153 281), lower := (rows 37 290 196 11 82 160 64 128 256), losses := [] }

theorem u27084 : Upper (D 7) (R 7) [36,288,192,3,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27085 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 196 11 88 33 210 146 402), lower := (rows 37 290 196 11 88 33 64 128 256), losses := [] }

theorem u27085 : Upper (D 7) (R 7) [36,288,192,3,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27086 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 290 196 11 88 34 209 145 401), lower := (rows 37 290 196 11 88 34 64 128 256), losses := [] }

theorem u27086 : Upper (D 7) (R 7) [36,288,192,3,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27087 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 3, region := 196, targets := 32 }], pairs := [(1,6),(2,5),(3,6)], upper := (rows 37 290 196 11 88 48 195 131 387), lower := (rows 37 290 196 11 88 48 64 128 256), losses := [] }

theorem u27087 : Upper (D 7) (R 7) [36,288,192,3,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27087 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27088 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 290 196 11 88 160 83 147 275), lower := (rows 37 290 196 11 88 160 64 128 256), losses := [] }

theorem u27088 : Upper (D 7) (R 7) [36,288,192,3,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27089 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 196 25 26 33 194 194 450), lower := (rows 37 290 196 25 26 33 64 128 256), losses := [] }

theorem u27089 : Upper (D 7) (R 7) [36,288,192,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27090 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 290 196 25 26 34 193 193 449), lower := (rows 37 290 196 25 26 34 64 128 256), losses := [] }

theorem u27090 : Upper (D 7) (R 7) [36,288,192,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27091 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 290 196 25 26 96 195 131 387), lower := (rows 37 290 196 25 26 96 64 128 256), losses := [] }

theorem u27091 : Upper (D 7) (R 7) [36,288,192,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27092 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 290 196 25 82 33 202 138 394), lower := (rows 37 290 196 25 82 33 64 128 256), losses := [] }

theorem u27092 : Upper (D 7) (R 7) [36,288,192,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27093 : PairBound 9 := { available := 137, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 290 196 25 82 34 201 137 393), lower := (rows 37 290 196 25 82 34 64 128 256), losses := [] }

theorem u27093 : Upper (D 7) (R 7) [36,288,192,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27094 : Route 9 := (fun mask => (mask,id))

def c27094 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27094 : Upper (D 7) (R 7) [36,288,192,17,66,8] 13 := by
  apply FastRouting.sound _ _ [36,288,192,17,66,8] 13 (by decide) (choices 1) [1,2,128] r27094 c27094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9912
  · exact u9913
  · exact u9914

def b27095 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 290 196 25 82 160 75 139 267), lower := (rows 37 290 196 25 82 160 64 128 256), losses := [] }

theorem u27095 : Upper (D 7) (R 7) [36,288,192,17,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27096 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 57, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 290 196 25 88 33 194 130 386), lower := (rows 37 290 196 25 88 33 64 128 256), losses := [] }

theorem u27096 : Upper (D 7) (R 7) [36,288,192,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27097 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 37 290 196 25 88 34 195 131 387), lower := (rows 37 290 196 25 88 34 64 128 256), losses := [] }

theorem u27097 : Upper (D 7) (R 7) [36,288,192,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27098 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 290 196 25 88 160 67 131 259), lower := (rows 37 290 196 25 88 160 64 128 256), losses := [] }

theorem u27098 : Upper (D 7) (R 7) [36,288,192,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27099 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 290 196 26 81 33 202 138 394), lower := (rows 37 290 196 26 81 33 64 128 256), losses := [] }

theorem u27099 : Upper (D 7) (R 7) [36,288,192,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27100 : PairBound 9 := { available := 137, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 37 290 196 26 81 34 201 137 393), lower := (rows 37 290 196 26 81 34 64 128 256), losses := [] }

theorem u27100 : Upper (D 7) (R 7) [36,288,192,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27101 : Route 9 := (fun mask => (mask,id))

def c27101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27101 : Upper (D 7) (R 7) [36,288,192,18,65,8] 13 := by
  apply FastRouting.sound _ _ [36,288,192,18,65,8] 13 (by decide) (choices 1) [1,2,128] r27101 c27101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9915
  · exact u9916
  · exact u9917

def b27102 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 290 196 26 81 160 75 139 267), lower := (rows 37 290 196 26 81 160 64 128 256), losses := [] }

theorem u27102 : Upper (D 7) (R 7) [36,288,192,18,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27103 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 290 196 26 88 33 195 131 387), lower := (rows 37 290 196 26 88 33 64 128 256), losses := [] }

theorem u27103 : Upper (D 7) (R 7) [36,288,192,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27104 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 290 196 26 88 34 193 129 385), lower := (rows 37 290 196 26 88 34 64 128 256), losses := [] }

theorem u27104 : Upper (D 7) (R 7) [36,288,192,18,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27105 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 290 196 26 88 160 67 131 259), lower := (rows 37 290 196 26 88 160 64 128 256), losses := [] }

theorem u27105 : Upper (D 7) (R 7) [36,288,192,18,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27106 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 290 196 73 146 33 90 154 282), lower := (rows 37 290 196 73 146 33 64 128 256), losses := [] }

theorem u27106 : Upper (D 7) (R 7) [36,288,192,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27107 : PairBound 9 := { available := 25, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 37 290 196 73 146 34 89 153 281), lower := (rows 37 290 196 73 146 34 64 128 256), losses := [] }

theorem u27107 : Upper (D 7) (R 7) [36,288,192,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27108 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 290 196 73 146 40 83 147 275), lower := (rows 37 290 196 73 146 40 64 128 256), losses := [] }

theorem u27108 : Upper (D 7) (R 7) [36,288,192,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27108 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27109 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(1,7),(3,7)], upper := (rows 37 290 196 73 146 48 75 139 267), lower := (rows 37 290 196 73 146 48 64 128 256), losses := [] }

theorem u27109 : Upper (D 7) (R 7) [36,288,192,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27109 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27110 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 57, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 37 290 196 73 152 33 82 146 274), lower := (rows 37 290 196 73 152 33 64 128 256), losses := [] }

theorem u27110 : Upper (D 7) (R 7) [36,288,192,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27111 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 37 290 196 73 152 34 83 147 275), lower := (rows 37 290 196 73 152 34 64 128 256), losses := [] }

theorem u27111 : Upper (D 7) (R 7) [36,288,192,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27112 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 290 196 73 152 48 67 131 259), lower := (rows 37 290 196 73 152 48 64 128 256), losses := [] }

theorem u27112 : Upper (D 7) (R 7) [36,288,192,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27112 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27113 : Route 9 := (fun mask => (mask,id))

def c27113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27113 : Upper (D 7) (R 7) [36,288,192,66,130,1] 13 := by
  apply FastRouting.sound _ _ [36,288,192,66,130,1] 13 (by decide) (choices 1) [1,8,16] r27113 c27113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9918
  · exact u9919
  · exact u9920

def r27114 : Route 9 := (fun mask => (mask,id))

def c27114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27114 : Upper (D 7) (R 7) [36,288,192,66,130,8] 13 := by
  apply FastRouting.sound _ _ [36,288,192,66,130,8] 13 (by decide) (choices 1) [1,16] r27114 c27114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9921
  · exact u9922

def r27115 : Route 9 := (fun mask => (mask,id))

def c27115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27115 : Upper (D 7) (R 7) [36,288,192,66,136,1] 13 := by
  apply FastRouting.sound _ _ [36,288,192,66,136,1] 13 (by decide) (choices 1) [1,2,16] r27115 c27115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9923
  · exact u9924
  · exact u9925

def r27116 : Route 9 := (fun mask => (mask,id))

def c27116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27116 : Upper (D 7) (R 7) [36,288,192,66,136,2] 13 := by
  apply FastRouting.sound _ _ [36,288,192,66,136,2] 13 (by decide) (choices 1) [1,16] r27116 c27116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9926
  · exact u9927

def b27117 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 0, region := 258, targets := 64 }], pairs := [(1,6),(1,7),(3,7)], upper := (rows 37 290 196 74 152 48 67 131 259), lower := (rows 37 290 196 74 152 48 64 128 256), losses := [] }

theorem u27117 : Upper (D 7) (R 7) [36,288,192,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27117 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27118 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 322 7 25 146 40 224 224 480), lower := (rows 37 322 7 25 146 40 64 128 256), losses := [] }

theorem u27118 : Upper (D 7) (R 7) [36,320,3,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27118 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27119 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 322 7 25 146 96 232 168 424), lower := (rows 37 322 7 25 146 96 64 128 256), losses := [] }

theorem u27119 : Upper (D 7) (R 7) [36,320,3,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27119
end Delivery.IrregularNine14.P07
