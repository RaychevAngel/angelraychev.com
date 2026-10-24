import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0418
import IrregularNine14P06C0419

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38940 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 292 11 21 124 92 220 348), lower := (rows 35 194 292 11 21 32 64 128 256), losses := [] }

theorem u38940 : Upper (D 6) (R 6) [34,192,288,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38941 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 292 11 25 116 84 212 340), lower := (rows 35 194 292 11 25 32 64 128 256), losses := [] }

theorem u38941 : Upper (D 6) (R 6) [34,192,288,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38942 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 292 11 28 117 85 213 341), lower := (rows 35 194 292 11 28 32 64 128 256), losses := [] }

theorem u38942 : Upper (D 6) (R 6) [34,192,288,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38943 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 292 11 81 60 92 156 284), lower := (rows 35 194 292 11 81 32 64 128 256), losses := [] }

theorem u38943 : Upper (D 6) (R 6) [34,192,288,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38944 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 292 11 84 61 93 157 285), lower := (rows 35 194 292 11 84 32 64 128 256), losses := [] }

theorem u38944 : Upper (D 6) (R 6) [34,192,288,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38945 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 292 11 88 53 85 149 277), lower := (rows 35 194 292 11 88 32 64 128 256), losses := [] }

theorem u38945 : Upper (D 6) (R 6) [34,192,288,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38946 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 16, targets := 66 },{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 35 194 292 13 21 122 90 218 346), lower := (rows 35 194 292 13 21 32 64 128 256), losses := [] }

theorem u38946 : Upper (D 6) (R 6) [34,192,288,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38947 : Route 9 := (fun mask => (mask,id))

def c38947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38947 : Upper (D 6) (R 6) [34,192,288,5,6] 13 := by
  apply FastRouting.sound _ _ [34,192,288,5,6] 13 (by decide) (choices 1) [1,8,16,64] r38947 c38947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25090
  · exact u25091
  · exact u25092
  · exact u25093

def b38948 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 292 13 25 118 86 214 342), lower := (rows 35 194 292 13 25 32 64 128 256), losses := [] }

theorem u38948 : Upper (D 6) (R 6) [34,192,288,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38949 : Route 9 := (fun mask => (mask,id))

def c38949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38949 : Upper (D 6) (R 6) [34,192,288,5,10] 13 := by
  apply FastRouting.sound _ _ [34,192,288,5,10] 13 (by decide) (choices 1) [1,4,16,64] r38949 c38949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25094
  · exact u25095
  · exact u25096
  · exact u25097

def b38950 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 292 13 28 115 83 211 339), lower := (rows 35 194 292 13 28 32 64 128 256), losses := [] }

theorem u38950 : Upper (D 6) (R 6) [34,192,288,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38951 : Route 9 := (fun mask => (mask,id))

def c38951 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38951 : Upper (D 6) (R 6) [34,192,288,5,65] 13 := by
  apply FastRouting.sound _ _ [34,192,288,5,65] 13 (by decide) (choices 1) [2,4,8,16] r38951 c38951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25098
  · exact u25099
  · exact u25100
  · exact u25101

def b38952 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 292 13 82 61 93 157 285), lower := (rows 35 194 292 13 82 32 64 128 256), losses := [] }

theorem u38952 : Upper (D 6) (R 6) [34,192,288,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38953 : Route 9 := (fun mask => (mask,id))

def c38953 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38953 : Upper (D 6) (R 6) [34,192,288,5,68] 13 := by
  apply FastRouting.sound _ _ [34,192,288,5,68] 13 (by decide) (choices 1) [1,2,8,16] r38953 c38953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25102
  · exact u25103
  · exact u25104
  · exact u25105

def r38954 : Route 9 := (fun mask => (mask,id))

def c38954 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38954 : Upper (D 6) (R 6) [34,192,288,5,72] 13 := by
  apply FastRouting.sound _ _ [34,192,288,5,72] 13 (by decide) (choices 1) [1,2,4,16] r38954 c38954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25106
  · exact u25107
  · exact u25108
  · exact u25109

def r38955 : Route 9 := (fun mask => (mask,id))

def c38955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38955 : Upper (D 6) (R 6) [34,192,288,6,9] 13 := by
  apply FastRouting.sound _ _ [34,192,288,6,9] 13 (by decide) (choices 1) [1,4,16,64] r38955 c38955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25110
  · exact u25111
  · exact u25112
  · exact u25113

def b38956 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 194 292 14 28 113 81 209 337), lower := (rows 35 194 292 14 28 32 64 128 256), losses := [] }

theorem u38956 : Upper (D 6) (R 6) [34,192,288,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38957 : Route 9 := (fun mask => (mask,id))

def c38957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38957 : Upper (D 6) (R 6) [34,192,288,6,65] 13 := by
  apply FastRouting.sound _ _ [34,192,288,6,65] 13 (by decide) (choices 1) [1,4,8,16] r38957 c38957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25114
  · exact u25115
  · exact u25116
  · exact u25117

def r38958 : Route 9 := (fun mask => (mask,id))

def c38958 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38958 : Upper (D 6) (R 6) [34,192,288,6,68] 13 := by
  apply FastRouting.sound _ _ [34,192,288,6,68] 13 (by decide) (choices 1) [1,8,16] r38958 c38958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25118
  · exact u25119
  · exact u25120

def r38959 : Route 9 := (fun mask => (mask,id))

def c38959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38959 : Upper (D 6) (R 6) [34,192,288,6,72] 13 := by
  apply FastRouting.sound _ _ [34,192,288,6,72] 13 (by decide) (choices 1) [1,4,16] r38959 c38959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25121
  · exact u25122
  · exact u25123

def b38960 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 292 25 25 102 70 198 326), lower := (rows 35 194 292 25 25 32 64 128 256), losses := [] }

theorem u38960 : Upper (D 6) (R 6) [34,192,288,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38961 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 292 25 26 101 69 197 325), lower := (rows 35 194 292 25 26 32 64 128 256), losses := [] }

theorem u38961 : Upper (D 6) (R 6) [34,192,288,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38962 : Route 9 := (fun mask => (mask,id))

def c38962 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38962 : Upper (D 6) (R 6) [34,192,288,17,12] 13 := by
  apply FastRouting.sound _ _ [34,192,288,17,12] 13 (by decide) (choices 1) [1,2,4,64] r38962 c38962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25124
  · exact u25125
  · exact u25126
  · exact u25127

def b38963 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 292 25 81 46 78 142 270), lower := (rows 35 194 292 25 81 32 64 128 256), losses := [] }

theorem u38963 : Upper (D 6) (R 6) [34,192,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38964 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 292 25 82 45 77 141 269), lower := (rows 35 194 292 25 82 32 64 128 256), losses := [] }

theorem u38964 : Upper (D 6) (R 6) [34,192,288,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38965 : Route 9 := (fun mask => (mask,id))

def c38965 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38965 : Upper (D 6) (R 6) [34,192,288,17,68] 13 := by
  apply FastRouting.sound _ _ [34,192,288,17,68] 13 (by decide) (choices 1) [1,2,4,8] r38965 c38965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25128
  · exact u25129
  · exact u25130
  · exact u25131

def r38966 : Route 9 := (fun mask => (mask,id))

def c38966 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38966 : Upper (D 6) (R 6) [34,192,288,17,72] 13 := by
  apply FastRouting.sound _ _ [34,192,288,17,72] 13 (by decide) (choices 1) [1,2,4] r38966 c38966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25132
  · exact u25133
  · exact u25134

def r38967 : Route 9 := (fun mask => (mask,id))

def c38967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38967 : Upper (D 6) (R 6) [34,192,288,18,12] 13 := by
  apply FastRouting.sound _ _ [34,192,288,18,12] 13 (by decide) (choices 1) [1,4,64] r38967 c38967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25135
  · exact u25136
  · exact u25137

def r38968 : Route 9 := (fun mask => (mask,id))

def c38968 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38968 : Upper (D 6) (R 6) [34,192,288,18,65] 13 := by
  apply FastRouting.sound _ _ [34,192,288,18,65] 13 (by decide) (choices 1) [1,4,8] r38968 c38968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25138
  · exact u25139
  · exact u25140

def r38969 : Route 9 := (fun mask => (mask,id))

def c38969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38969 : Upper (D 6) (R 6) [34,192,288,18,68] 13 := by
  apply FastRouting.sound _ _ [34,192,288,18,68] 13 (by decide) (choices 1) [1,4,8] r38969 c38969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25141
  · exact u25142
  · exact u25143

def b38970 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 194 292 26 88 37 69 133 261), lower := (rows 35 194 292 26 88 32 64 128 256), losses := [] }

theorem u38970 : Upper (D 6) (R 6) [34,192,288,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38971 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 292 28 28 99 67 195 323), lower := (rows 35 194 292 28 28 32 64 128 256), losses := [] }

theorem u38971 : Upper (D 6) (R 6) [34,192,288,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38972 : Route 9 := (fun mask => (mask,id))

def c38972 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38972 : Upper (D 6) (R 6) [34,192,288,20,65] 13 := by
  apply FastRouting.sound _ _ [34,192,288,20,65] 13 (by decide) (choices 1) [1,2,4,8] r38972 c38972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25144
  · exact u25145
  · exact u25146
  · exact u25147

def b38973 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 292 28 82 45 77 141 269), lower := (rows 35 194 292 28 82 32 64 128 256), losses := [] }

theorem u38973 : Upper (D 6) (R 6) [34,192,288,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38974 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 292 28 84 43 75 139 267), lower := (rows 35 194 292 28 84 32 64 128 256), losses := [] }

theorem u38974 : Upper (D 6) (R 6) [34,192,288,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38975 : Route 9 := (fun mask => (mask,id))

def c38975 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38975 : Upper (D 6) (R 6) [34,192,288,20,72] 13 := by
  apply FastRouting.sound _ _ [34,192,288,20,72] 13 (by decide) (choices 1) [1,2,4] r38975 c38975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25148
  · exact u25149
  · exact u25150

def b38976 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 324 11 21 60 124 188 316), lower := (rows 35 194 324 11 21 32 64 128 256), losses := [] }

theorem u38976 : Upper (D 6) (R 6) [34,192,320,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38977 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 324 11 25 52 116 180 308), lower := (rows 35 194 324 11 25 32 64 128 256), losses := [] }

theorem u38977 : Upper (D 6) (R 6) [34,192,320,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38978 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 324 11 28 53 117 181 309), lower := (rows 35 194 324 11 28 32 64 128 256), losses := [] }

theorem u38978 : Upper (D 6) (R 6) [34,192,320,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38979 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 324 11 52 61 93 157 285), lower := (rows 35 194 324 11 52 32 64 128 256), losses := [] }

theorem u38979 : Upper (D 6) (R 6) [34,192,320,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38980 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 324 11 56 53 85 149 277), lower := (rows 35 194 324 11 56 32 64 128 256), losses := [] }

theorem u38980 : Upper (D 6) (R 6) [34,192,320,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38981 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 194 324 13 21 58 122 186 314), lower := (rows 35 194 324 13 21 32 64 128 256), losses := [] }

theorem u38981 : Upper (D 6) (R 6) [34,192,320,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38982 : Route 9 := (fun mask => (mask,id))

def c38982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38982 : Upper (D 6) (R 6) [34,192,320,5,6] 13 := by
  apply FastRouting.sound _ _ [34,192,320,5,6] 13 (by decide) (choices 1) [1,8,16] r38982 c38982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25151
  · exact u25152
  · exact u25153

def b38983 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 194 324 13 25 54 118 182 310), lower := (rows 35 194 324 13 25 32 64 128 256), losses := [] }

theorem u38983 : Upper (D 6) (R 6) [34,192,320,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38984 : Route 9 := (fun mask => (mask,id))

def c38984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38984 : Upper (D 6) (R 6) [34,192,320,5,10] 13 := by
  apply FastRouting.sound _ _ [34,192,320,5,10] 13 (by decide) (choices 1) [1,4,16] r38984 c38984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25154
  · exact u25155
  · exact u25156

def b38985 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 194 324 13 28 51 115 179 307), lower := (rows 35 194 324 13 28 32 64 128 256), losses := [] }

theorem u38985 : Upper (D 6) (R 6) [34,192,320,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38986 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 324 13 49 62 94 158 286), lower := (rows 35 194 324 13 49 32 64 128 256), losses := [] }

theorem u38986 : Upper (D 6) (R 6) [34,192,320,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38987 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 324 13 50 61 93 157 285), lower := (rows 35 194 324 13 50 32 64 128 256), losses := [] }

theorem u38987 : Upper (D 6) (R 6) [34,192,320,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38988 : Route 9 := (fun mask => (mask,id))

def c38988 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38988 : Upper (D 6) (R 6) [34,192,320,5,36] 13 := by
  apply FastRouting.sound _ _ [34,192,320,5,36] 13 (by decide) (choices 1) [1,2,8,16] r38988 c38988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25157
  · exact u25158
  · exact u25159
  · exact u25160

def r38989 : Route 9 := (fun mask => (mask,id))

def c38989 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38989 : Upper (D 6) (R 6) [34,192,320,5,40] 13 := by
  apply FastRouting.sound _ _ [34,192,320,5,40] 13 (by decide) (choices 1) [1,2,4,16] r38989 c38989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25161
  · exact u25162
  · exact u25163
  · exact u25164

def b38990 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 49, targets := 64 },{ cop := 4, region := 356, targets := 2 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 35 194 324 14 25 53 117 181 309), lower := (rows 35 194 324 14 25 32 64 128 256), losses := [] }

theorem u38990 : Upper (D 6) (R 6) [34,192,320,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38991 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 194 324 14 28 49 113 177 305), lower := (rows 35 194 324 14 28 32 64 128 256), losses := [] }

theorem u38991 : Upper (D 6) (R 6) [34,192,320,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38992 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 324 14 49 61 93 157 285), lower := (rows 35 194 324 14 49 32 64 128 256), losses := [] }

theorem u38992 : Upper (D 6) (R 6) [34,192,320,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38993 : Route 9 := (fun mask => (mask,id))

def c38993 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38993 : Upper (D 6) (R 6) [34,192,320,6,36] 13 := by
  apply FastRouting.sound _ _ [34,192,320,6,36] 13 (by decide) (choices 1) [1,8,16] r38993 c38993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25165
  · exact u25166
  · exact u25167

def r38994 : Route 9 := (fun mask => (mask,id))

def c38994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38994 : Upper (D 6) (R 6) [34,192,320,6,40] 13 := by
  apply FastRouting.sound _ _ [34,192,320,6,40] 13 (by decide) (choices 1) [1,4,16] r38994 c38994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25168
  · exact u25169
  · exact u25170

def b38995 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 324 25 25 38 102 166 294), lower := (rows 35 194 324 25 25 32 64 128 256), losses := [] }

theorem u38995 : Upper (D 6) (R 6) [34,192,320,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38996 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 324 25 26 37 101 165 293), lower := (rows 35 194 324 25 26 32 64 128 256), losses := [] }

theorem u38996 : Upper (D 6) (R 6) [34,192,320,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38997 : Route 9 := (fun mask => (mask,id))

def c38997 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38997 : Upper (D 6) (R 6) [34,192,320,17,12] 13 := by
  apply FastRouting.sound _ _ [34,192,320,17,12] 13 (by decide) (choices 1) [1,2,4] r38997 c38997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25171
  · exact u25172
  · exact u25173

def b38998 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 324 25 49 46 78 142 270), lower := (rows 35 194 324 25 49 32 64 128 256), losses := [] }

theorem u38998 : Upper (D 6) (R 6) [34,192,320,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38999 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 324 25 50 45 77 141 269), lower := (rows 35 194 324 25 50 32 64 128 256), losses := [] }

theorem u38999 : Upper (D 6) (R 6) [34,192,320,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u38999
end Delivery.IrregularNine14.P06
