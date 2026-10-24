import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0448
import IrregularNine14P06C0449

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40080 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 25, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 25 49 102 70 198 326), lower := (rows 41 134 324 25 49 32 64 128 256), losses := [] }

theorem u40080 : Upper (D 6) (R 6) [40,132,320,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40081 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 25 50 103 71 199 327), lower := (rows 41 134 324 25 50 32 64 128 256), losses := [] }

theorem u40081 : Upper (D 6) (R 6) [40,132,320,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40082 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 25 52 99 67 195 323), lower := (rows 41 134 324 25 52 32 64 128 256), losses := [] }

theorem u40082 : Upper (D 6) (R 6) [40,132,320,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40083 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 134 324 25 81 38 102 166 294), lower := (rows 41 134 324 25 81 32 64 128 256), losses := [] }

theorem u40083 : Upper (D 6) (R 6) [40,132,320,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40084 : Route 9 := (fun mask => (mask,id))

def c40084 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40084 : Upper (D 6) (R 6) [40,132,320,17,66] 13 := by
  apply FastRouting.sound _ _ [40,132,320,17,66] 13 (by decide) (choices 1) [1,2,4] r40084 c40084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26888
  · exact u26889
  · exact u26890

def b40085 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 134 324 25 84 35 99 163 291), lower := (rows 41 134 324 25 84 32 64 128 256), losses := [] }

theorem u40085 : Upper (D 6) (R 6) [40,132,320,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40086 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 25 112 39 71 135 263), lower := (rows 41 134 324 25 112 32 64 128 256), losses := [] }

theorem u40086 : Upper (D 6) (R 6) [40,132,320,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40087 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 134 324 26 19 101 101 229 357), lower := (rows 41 134 324 26 19 32 64 128 256), losses := [] }

theorem u40087 : Upper (D 6) (R 6) [40,132,320,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40088 : Route 9 := (fun mask => (mask,id))

def c40088 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40088 : Upper (D 6) (R 6) [40,132,320,18,5] 13 := by
  apply FastRouting.sound _ _ [40,132,320,18,5] 13 (by decide) (choices 1) [1,2,64] r40088 c40088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26891
  · exact u26892
  · exact u26893

def b40089 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 41 134 324 26 22 97 97 225 353), lower := (rows 41 134 324 26 22 32 64 128 256), losses := [] }

theorem u40089 : Upper (D 6) (R 6) [40,132,320,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40090 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 324 26 49 103 71 199 327), lower := (rows 41 134 324 26 49 32 64 128 256), losses := [] }

theorem u40090 : Upper (D 6) (R 6) [40,132,320,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40091 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 324 26 50 101 69 197 325), lower := (rows 41 134 324 26 50 32 64 128 256), losses := [] }

theorem u40091 : Upper (D 6) (R 6) [40,132,320,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40092 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 41 134 324 26 52 99 67 195 323), lower := (rows 41 134 324 26 52 32 64 128 256), losses := [] }

theorem u40092 : Upper (D 6) (R 6) [40,132,320,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40093 : Route 9 := (fun mask => (mask,id))

def c40093 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40093 : Upper (D 6) (R 6) [40,132,320,18,65] 13 := by
  apply FastRouting.sound _ _ [40,132,320,18,65] 13 (by decide) (choices 1) [1,2,4] r40093 c40093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26894
  · exact u26895
  · exact u26896

def b40094 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 134 324 26 82 37 101 165 293), lower := (rows 41 134 324 26 82 32 64 128 256), losses := [] }

theorem u40094 : Upper (D 6) (R 6) [40,132,320,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40095 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 134 324 26 84 35 99 163 291), lower := (rows 41 134 324 26 84 32 64 128 256), losses := [] }

theorem u40095 : Upper (D 6) (R 6) [40,132,320,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40096 : Route 9 := (fun mask => (mask,id))

def c40096 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40096 : Upper (D 6) (R 6) [40,132,320,18,96] 13 := by
  apply FastRouting.sound _ _ [40,132,320,18,96] 13 (by decide) (choices 1) [1,2,4] r40096 c40096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26897
  · exact u26898
  · exact u26899

def r40097 : Route 9 := (fun mask => (mask,id))

def c40097 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40097 : Upper (D 6) (R 6) [40,132,320,20,3] 13 := by
  apply FastRouting.sound _ _ [40,132,320,20,3] 13 (by decide) (choices 1) [1,2,64] r40097 c40097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26900
  · exact u26901
  · exact u26902

def b40098 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 324 28 49 99 67 195 323), lower := (rows 41 134 324 28 49 32 64 128 256), losses := [] }

theorem u40098 : Upper (D 6) (R 6) [40,132,320,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40099 : Route 9 := (fun mask => (mask,id))

def c40099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40099 : Upper (D 6) (R 6) [40,132,320,20,34] 13 := by
  apply FastRouting.sound _ _ [40,132,320,20,34] 13 (by decide) (choices 1) [1,2,64] r40099 c40099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26903
  · exact u26904
  · exact u26905

def r40100 : Route 9 := (fun mask => (mask,id))

def c40100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40100 : Upper (D 6) (R 6) [40,132,320,20,65] 13 := by
  apply FastRouting.sound _ _ [40,132,320,20,65] 13 (by decide) (choices 1) [1,2] r40100 c40100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26906
  · exact u26907

def r40101 : Route 9 := (fun mask => (mask,id))

def c40101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40101 : Upper (D 6) (R 6) [40,132,320,20,66] 13 := by
  apply FastRouting.sound _ _ [40,132,320,20,66] 13 (by decide) (choices 1) [1,2] r40101 c40101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26908
  · exact u26909

def b40102 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 41 134 324 28 112 35 67 131 259), lower := (rows 41 134 324 28 112 32 64 128 256), losses := [] }

theorem u40102 : Upper (D 6) (R 6) [40,132,320,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40103 : Route 9 := (fun mask => (mask,id))

def c40103 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40103 : Upper (D 6) (R 6) [40,132,320,65,3] 13 := by
  apply FastRouting.sound _ _ [40,132,320,65,3] 13 (by decide) (choices 1) [2,4,16] r40103 c40103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26910
  · exact u26911
  · exact u26912

def b40104 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 41 134 324 73 21 50 114 178 306), lower := (rows 41 134 324 73 21 32 64 128 256), losses := [] }

theorem u40104 : Upper (D 6) (R 6) [40,132,320,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40105 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 324 73 22 51 115 179 307), lower := (rows 41 134 324 73 22 32 64 128 256), losses := [] }

theorem u40105 : Upper (D 6) (R 6) [40,132,320,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40106 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 324 73 49 54 86 150 278), lower := (rows 41 134 324 73 49 32 64 128 256), losses := [] }

theorem u40106 : Upper (D 6) (R 6) [40,132,320,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40107 : Route 9 := (fun mask => (mask,id))

def c40107 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40107 : Upper (D 6) (R 6) [40,132,320,65,34] 13 := by
  apply FastRouting.sound _ _ [40,132,320,65,34] 13 (by decide) (choices 1) [1,2,4,16] r40107 c40107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26913
  · exact u26914
  · exact u26915
  · exact u26916

def r40108 : Route 9 := (fun mask => (mask,id))

def c40108 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40108 : Upper (D 6) (R 6) [40,132,320,65,36] 13 := by
  apply FastRouting.sound _ _ [40,132,320,65,36] 13 (by decide) (choices 1) [1,2,16] r40108 c40108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26917
  · exact u26918
  · exact u26919

def r40109 : Route 9 := (fun mask => (mask,id))

def c40109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40109 : Upper (D 6) (R 6) [40,132,320,66,3] 13 := by
  apply FastRouting.sound _ _ [40,132,320,66,3] 13 (by decide) (choices 1) [1,4,16] r40109 c40109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26920
  · exact u26921
  · exact u26922

def r40110 : Route 9 := (fun mask => (mask,id))

def c40110 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40110 : Upper (D 6) (R 6) [40,132,320,66,5] 13 := by
  apply FastRouting.sound _ _ [40,132,320,66,5] 13 (by decide) (choices 1) [1,2,16] r40110 c40110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26923
  · exact u26924
  · exact u26925

def b40111 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 324 74 22 49 113 177 305), lower := (rows 41 134 324 74 22 32 64 128 256), losses := [] }

theorem u40111 : Upper (D 6) (R 6) [40,132,320,66,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40112 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 324 74 49 55 87 151 279), lower := (rows 41 134 324 74 49 32 64 128 256), losses := [] }

theorem u40112 : Upper (D 6) (R 6) [40,132,320,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40113 : Route 9 := (fun mask => (mask,id))

def c40113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40113 : Upper (D 6) (R 6) [40,132,320,66,34] 13 := by
  apply FastRouting.sound _ _ [40,132,320,66,34] 13 (by decide) (choices 1) [1,4,16] r40113 c40113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26926
  · exact u26927
  · exact u26928

def r40114 : Route 9 := (fun mask => (mask,id))

def c40114 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40114 : Upper (D 6) (R 6) [40,132,320,66,36] 13 := by
  apply FastRouting.sound _ _ [40,132,320,66,36] 13 (by decide) (choices 1) [1,2,16] r40114 c40114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26929
  · exact u26930
  · exact u26931

def r40115 : Route 9 := (fun mask => (mask,id))

def c40115 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40115 : Upper (D 6) (R 6) [40,132,320,80,3] 13 := by
  apply FastRouting.sound _ _ [40,132,320,80,3] 13 (by decide) (choices 1) [1,2,4] r40115 c40115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26932
  · exact u26933
  · exact u26934

def r40116 : Route 9 := (fun mask => (mask,id))

def c40116 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40116 : Upper (D 6) (R 6) [40,132,320,80,5] 13 := by
  apply FastRouting.sound _ _ [40,132,320,80,5] 13 (by decide) (choices 1) [1,2] r40116 c40116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26935
  · exact u26936

def b40117 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 324 88 22 35 99 163 291), lower := (rows 41 134 324 88 22 32 64 128 256), losses := [] }

theorem u40117 : Upper (D 6) (R 6) [40,132,320,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40118 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 324 88 49 39 71 135 263), lower := (rows 41 134 324 88 49 32 64 128 256), losses := [] }

theorem u40118 : Upper (D 6) (R 6) [40,132,320,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40119 : Route 9 := (fun mask => (mask,id))

def c40119 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40119 : Upper (D 6) (R 6) [40,132,320,80,34] 13 := by
  apply FastRouting.sound _ _ [40,132,320,80,34] 13 (by decide) (choices 1) [1,2,4] r40119 c40119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26937
  · exact u26938
  · exact u26939

def r40120 : Route 9 := (fun mask => (mask,id))

def c40120 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40120 : Upper (D 6) (R 6) [40,132,320,80,36] 13 := by
  apply FastRouting.sound _ _ [40,132,320,80,36] 13 (by decide) (choices 1) [1,2] r40120 c40120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26940
  · exact u26941

def b40121 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 146 292 11 19 100 68 196 324), lower := (rows 41 146 292 11 19 32 64 128 256), losses := [] }

theorem u40121 : Upper (D 6) (R 6) [40,144,288,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40122 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 146 292 11 21 102 70 198 326), lower := (rows 41 146 292 11 21 32 64 128 256), losses := [] }

theorem u40122 : Upper (D 6) (R 6) [40,144,288,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40123 : Route 9 := (fun mask => (mask,id))

def c40123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40123 : Upper (D 6) (R 6) [40,144,288,3,6] 13 := by
  apply FastRouting.sound _ _ [40,144,288,3,6] 13 (by decide) (choices 1) [1,4,64] r40123 c40123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26942
  · exact u26943
  · exact u26944

def r40124 : Route 9 := (fun mask => (mask,id))

def c40124 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40124 : Upper (D 6) (R 6) [40,144,288,3,65] 13 := by
  apply FastRouting.sound _ _ [40,144,288,3,65] 13 (by decide) (choices 1) [2,4,64] r40124 c40124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26945
  · exact u26946
  · exact u26947

def r40125 : Route 9 := (fun mask => (mask,id))

def c40125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40125 : Upper (D 6) (R 6) [40,144,288,3,66] 13 := by
  apply FastRouting.sound _ _ [40,144,288,3,66] 13 (by decide) (choices 1) [1,4,64] r40125 c40125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26948
  · exact u26949
  · exact u26950

def r40126 : Route 9 := (fun mask => (mask,id))

def c40126 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40126 : Upper (D 6) (R 6) [40,144,288,3,68] 13 := by
  apply FastRouting.sound _ _ [40,144,288,3,68] 13 (by decide) (choices 1) [1,2,4,64] r40126 c40126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26951
  · exact u26952
  · exact u26953
  · exact u26954

def r40127 : Route 9 := (fun mask => (mask,id))

def c40127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40127 : Upper (D 6) (R 6) [40,144,288,6,3] 13 := by
  apply FastRouting.sound _ _ [40,144,288,6,3] 13 (by decide) (choices 1) [1,4,64] r40127 c40127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26955
  · exact u26956
  · exact u26957

def b40128 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 202, targets := 32 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(3,5)], upper := (rows 41 146 292 14 21 99 67 195 323), lower := (rows 41 146 292 14 21 32 64 128 256), losses := [] }

theorem u40128 : Upper (D 6) (R 6) [40,144,288,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40129 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 146 292 14 22 97 65 193 321), lower := (rows 41 146 292 14 22 32 64 128 256), losses := [] }

theorem u40129 : Upper (D 6) (R 6) [40,144,288,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40130 : Route 9 := (fun mask => (mask,id))

def c40130 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40130 : Upper (D 6) (R 6) [40,144,288,6,65] 13 := by
  apply FastRouting.sound _ _ [40,144,288,6,65] 13 (by decide) (choices 1) [1,2,4,64] r40130 c40130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26958
  · exact u26959
  · exact u26960
  · exact u26961

def r40131 : Route 9 := (fun mask => (mask,id))

def c40131 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40131 : Upper (D 6) (R 6) [40,144,288,6,66] 13 := by
  apply FastRouting.sound _ _ [40,144,288,6,66] 13 (by decide) (choices 1) [1,4,64] r40131 c40131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26962
  · exact u26963
  · exact u26964

def r40132 : Route 9 := (fun mask => (mask,id))

def c40132 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40132 : Upper (D 6) (R 6) [40,144,288,6,68] 13 := by
  apply FastRouting.sound _ _ [40,144,288,6,68] 13 (by decide) (choices 1) [1,2,64] r40132 c40132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26965
  · exact u26966
  · exact u26967

def r40133 : Route 9 := (fun mask => (mask,id))

def c40133 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40133 : Upper (D 6) (R 6) [40,144,288,65,3] 13 := by
  apply FastRouting.sound _ _ [40,144,288,65,3] 13 (by decide) (choices 1) [2,4,64] r40133 c40133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26968
  · exact u26969
  · exact u26970

def b40134 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 146 292 73 21 102 70 198 326), lower := (rows 41 146 292 73 21 32 64 128 256), losses := [] }

theorem u40134 : Upper (D 6) (R 6) [40,144,288,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40135 : Route 9 := (fun mask => (mask,id))

def c40135 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40135 : Upper (D 6) (R 6) [40,144,288,65,6] 13 := by
  apply FastRouting.sound _ _ [40,144,288,65,6] 13 (by decide) (choices 1) [1,2,4,64] r40135 c40135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26971
  · exact u26972
  · exact u26973
  · exact u26974

def b40136 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 41 146 292 73 81 38 70 134 262), lower := (rows 41 146 292 73 81 32 64 128 256), losses := [] }

theorem u40136 : Upper (D 6) (R 6) [40,144,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40137 : Route 9 := (fun mask => (mask,id))

def c40137 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40137 : Upper (D 6) (R 6) [40,144,288,65,66] 13 := by
  apply FastRouting.sound _ _ [40,144,288,65,66] 13 (by decide) (choices 1) [1,2,4] r40137 c40137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26975
  · exact u26976
  · exact u26977

def r40138 : Route 9 := (fun mask => (mask,id))

def c40138 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40138 : Upper (D 6) (R 6) [40,144,288,65,68] 13 := by
  apply FastRouting.sound _ _ [40,144,288,65,68] 13 (by decide) (choices 1) [1,2,4] r40138 c40138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26978
  · exact u26979
  · exact u26980

def r40139 : Route 9 := (fun mask => (mask,id))

def c40139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40139 : Upper (D 6) (R 6) [40,144,288,66,3] 13 := by
  apply FastRouting.sound _ _ [40,144,288,66,3] 13 (by decide) (choices 1) [1,4,64] r40139 c40139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26981
  · exact u26982
  · exact u26983

#print axioms u40139
end Delivery.IrregularNine14.P06
