import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0451
import IrregularNine14P06C0452

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40200 : Route 9 := (fun mask => (mask,id))

def c40200 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40200 : Upper (D 6) (R 6) [40,160,320,6,5] 13 := by
  apply FastRouting.sound _ _ [40,160,320,6,5] 13 (by decide) (choices 1) [1,2,16,64] r40200 c40200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27089
  · exact u27090
  · exact u27091
  · exact u27092

def b40201 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 162 324 14 22 113 81 209 337), lower := (rows 41 162 324 14 22 32 64 128 256), losses := [] }

theorem u40201 : Upper (D 6) (R 6) [40,160,320,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40202 : Route 9 := (fun mask => (mask,id))

def c40202 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40202 : Upper (D 6) (R 6) [40,160,320,6,65] 13 := by
  apply FastRouting.sound _ _ [40,160,320,6,65] 13 (by decide) (choices 1) [1,2,4,16] r40202 c40202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27093
  · exact u27094
  · exact u27095
  · exact u27096

def r40203 : Route 9 := (fun mask => (mask,id))

def c40203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40203 : Upper (D 6) (R 6) [40,160,320,6,66] 13 := by
  apply FastRouting.sound _ _ [40,160,320,6,66] 13 (by decide) (choices 1) [1,4,16] r40203 c40203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27097
  · exact u27098
  · exact u27099

def b40204 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 162 324 14 84 51 83 147 275), lower := (rows 41 162 324 14 84 32 64 128 256), losses := [] }

theorem u40204 : Upper (D 6) (R 6) [40,160,320,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40205 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 162 324 25 19 102 70 198 326), lower := (rows 41 162 324 25 19 32 64 128 256), losses := [] }

theorem u40205 : Upper (D 6) (R 6) [40,160,320,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40206 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 162 324 25 21 102 70 198 326), lower := (rows 41 162 324 25 21 32 64 128 256), losses := [] }

theorem u40206 : Upper (D 6) (R 6) [40,160,320,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40207 : Route 9 := (fun mask => (mask,id))

def c40207 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40207 : Upper (D 6) (R 6) [40,160,320,17,6] 13 := by
  apply FastRouting.sound _ _ [40,160,320,17,6] 13 (by decide) (choices 1) [1,2,4,64] r40207 c40207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27100
  · exact u27101
  · exact u27102
  · exact u27103

def b40208 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 162 324 25 81 38 70 134 262), lower := (rows 41 162 324 25 81 32 64 128 256), losses := [] }

theorem u40208 : Upper (D 6) (R 6) [40,160,320,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40209 : Route 9 := (fun mask => (mask,id))

def c40209 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40209 : Upper (D 6) (R 6) [40,160,320,17,66] 13 := by
  apply FastRouting.sound _ _ [40,160,320,17,66] 13 (by decide) (choices 1) [1,2,4] r40209 c40209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27104
  · exact u27105
  · exact u27106

def b40210 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 162 324 25 84 39 71 135 263), lower := (rows 41 162 324 25 84 32 64 128 256), losses := [] }

theorem u40210 : Upper (D 6) (R 6) [40,160,320,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40211 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 162 324 26 19 101 69 197 325), lower := (rows 41 162 324 26 19 32 64 128 256), losses := [] }

theorem u40211 : Upper (D 6) (R 6) [40,160,320,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40212 : Route 9 := (fun mask => (mask,id))

def c40212 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40212 : Upper (D 6) (R 6) [40,160,320,18,5] 13 := by
  apply FastRouting.sound _ _ [40,160,320,18,5] 13 (by decide) (choices 1) [1,2,4,64] r40212 c40212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27107
  · exact u27108
  · exact u27109
  · exact u27110

def b40213 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 162 324 26 22 101 69 197 325), lower := (rows 41 162 324 26 22 32 64 128 256), losses := [] }

theorem u40213 : Upper (D 6) (R 6) [40,160,320,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40214 : Route 9 := (fun mask => (mask,id))

def c40214 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40214 : Upper (D 6) (R 6) [40,160,320,18,65] 13 := by
  apply FastRouting.sound _ _ [40,160,320,18,65] 13 (by decide) (choices 1) [1,2,4] r40214 c40214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27111
  · exact u27112
  · exact u27113

def b40215 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 162 324 26 82 37 69 133 261), lower := (rows 41 162 324 26 82 32 64 128 256), losses := [] }

theorem u40215 : Upper (D 6) (R 6) [40,160,320,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40216 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 162 324 26 84 39 71 135 263), lower := (rows 41 162 324 26 84 32 64 128 256), losses := [] }

theorem u40216 : Upper (D 6) (R 6) [40,160,320,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40217 : Route 9 := (fun mask => (mask,id))

def c40217 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40217 : Upper (D 6) (R 6) [40,160,320,20,3] 13 := by
  apply FastRouting.sound _ _ [40,160,320,20,3] 13 (by decide) (choices 1) [1,2,4,64] r40217 c40217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27114
  · exact u27115
  · exact u27116
  · exact u27117

def b40218 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 162 324 28 21 99 67 195 323), lower := (rows 41 162 324 28 21 32 64 128 256), losses := [] }

theorem u40218 : Upper (D 6) (R 6) [40,160,320,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40219 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 162 324 28 22 99 67 195 323), lower := (rows 41 162 324 28 22 32 64 128 256), losses := [] }

theorem u40219 : Upper (D 6) (R 6) [40,160,320,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40220 : Route 9 := (fun mask => (mask,id))

def c40220 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40220 : Upper (D 6) (R 6) [40,160,320,20,65] 13 := by
  apply FastRouting.sound _ _ [40,160,320,20,65] 13 (by decide) (choices 1) [1,2,4] r40220 c40220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27118
  · exact u27119
  · exact u27120

def r40221 : Route 9 := (fun mask => (mask,id))

def c40221 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40221 : Upper (D 6) (R 6) [40,160,320,20,66] 13 := by
  apply FastRouting.sound _ _ [40,160,320,20,66] 13 (by decide) (choices 1) [1,2,4] r40221 c40221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27121
  · exact u27122
  · exact u27123

def b40222 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 162 324 28 84 35 67 131 259), lower := (rows 41 162 324 28 84 32 64 128 256), losses := [] }

theorem u40222 : Upper (D 6) (R 6) [40,160,320,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40223 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 324, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 162 324 73 19 54 86 150 278), lower := (rows 41 162 324 73 19 32 64 128 256), losses := [] }

theorem u40223 : Upper (D 6) (R 6) [40,160,320,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40224 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 41 162 324 73 21 54 86 150 278), lower := (rows 41 162 324 73 21 32 64 128 256), losses := [] }

theorem u40224 : Upper (D 6) (R 6) [40,160,320,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40225 : Route 9 := (fun mask => (mask,id))

def c40225 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40225 : Upper (D 6) (R 6) [40,160,320,65,6] 13 := by
  apply FastRouting.sound _ _ [40,160,320,65,6] 13 (by decide) (choices 1) [1,2,4,16] r40225 c40225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27124
  · exact u27125
  · exact u27126
  · exact u27127

def b40226 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 332, targets := 32 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(3,5)], upper := (rows 41 162 324 74 19 53 85 149 277), lower := (rows 41 162 324 74 19 32 64 128 256), losses := [] }

theorem u40226 : Upper (D 6) (R 6) [40,160,320,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40227 : Route 9 := (fun mask => (mask,id))

def c40227 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40227 : Upper (D 6) (R 6) [40,160,320,66,5] 13 := by
  apply FastRouting.sound _ _ [40,160,320,66,5] 13 (by decide) (choices 1) [1,2,4,16] r40227 c40227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27128
  · exact u27129
  · exact u27130
  · exact u27131

def r40228 : Route 9 := (fun mask => (mask,id))

def c40228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40228 : Upper (D 6) (R 6) [40,160,320,66,6] 13 := by
  apply FastRouting.sound _ _ [40,160,320,66,6] 13 (by decide) (choices 1) [1,4,16] r40228 c40228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27132
  · exact u27133
  · exact u27134

def r40229 : Route 9 := (fun mask => (mask,id))

def c40229 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40229 : Upper (D 6) (R 6) [40,160,320,80,3] 13 := by
  apply FastRouting.sound _ _ [40,160,320,80,3] 13 (by decide) (choices 1) [1,2,4] r40229 c40229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27135
  · exact u27136
  · exact u27137

def r40230 : Route 9 := (fun mask => (mask,id))

def c40230 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40230 : Upper (D 6) (R 6) [40,160,320,80,5] 13 := by
  apply FastRouting.sound _ _ [40,160,320,80,5] 13 (by decide) (choices 1) [1,2,4] r40230 c40230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27138
  · exact u27139
  · exact u27140

def r40231 : Route 9 := (fun mask => (mask,id))

def c40231 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40231 : Upper (D 6) (R 6) [40,160,320,80,6] 13 := by
  apply FastRouting.sound _ _ [40,160,320,80,6] 13 (by decide) (choices 1) [1,2,4] r40231 c40231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27141
  · exact u27142
  · exact u27143

def b40232 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 194 324 11 19 52 116 180 308), lower := (rows 41 194 324 11 19 32 64 128 256), losses := [] }

theorem u40232 : Upper (D 6) (R 6) [40,192,320,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40233 : Route 9 := (fun mask => (mask,id))

def c40233 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40233 : Upper (D 6) (R 6) [40,192,320,3,5] 13 := by
  apply FastRouting.sound _ _ [40,192,320,3,5] 13 (by decide) (choices 1) [2,4,16] r40233 c40233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27144
  · exact u27145
  · exact u27146

def r40234 : Route 9 := (fun mask => (mask,id))

def c40234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40234 : Upper (D 6) (R 6) [40,192,320,3,6] 13 := by
  apply FastRouting.sound _ _ [40,192,320,3,6] 13 (by decide) (choices 1) [1,4,16] r40234 c40234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27147
  · exact u27148
  · exact u27149

def b40235 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 194 324 11 49 54 86 150 278), lower := (rows 41 194 324 11 49 32 64 128 256), losses := [] }

theorem u40235 : Upper (D 6) (R 6) [40,192,320,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40236 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 194 324 11 50 53 85 149 277), lower := (rows 41 194 324 11 50 32 64 128 256), losses := [] }

theorem u40236 : Upper (D 6) (R 6) [40,192,320,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40237 : Route 9 := (fun mask => (mask,id))

def c40237 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40237 : Upper (D 6) (R 6) [40,192,320,3,36] 13 := by
  apply FastRouting.sound _ _ [40,192,320,3,36] 13 (by decide) (choices 1) [1,2,4,16] r40237 c40237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27150
  · exact u27151
  · exact u27152
  · exact u27153

def b40238 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 49, targets := 64 },{ cop := 4, region := 356, targets := 2 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 41 194 324 14 19 53 117 181 309), lower := (rows 41 194 324 14 19 32 64 128 256), losses := [] }

theorem u40238 : Upper (D 6) (R 6) [40,192,320,6,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40239 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 33 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,6),(4,0),(4,5)], upper := (rows 41 194 324 14 22 49 113 177 305), lower := (rows 41 194 324 14 22 32 64 128 256), losses := [] }

theorem u40239 : Upper (D 6) (R 6) [40,192,320,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40240 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 194 324 14 49 55 87 151 279), lower := (rows 41 194 324 14 49 32 64 128 256), losses := [] }

theorem u40240 : Upper (D 6) (R 6) [40,192,320,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40241 : Route 9 := (fun mask => (mask,id))

def c40241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40241 : Upper (D 6) (R 6) [40,192,320,6,34] 13 := by
  apply FastRouting.sound _ _ [40,192,320,6,34] 13 (by decide) (choices 1) [1,4,16] r40241 c40241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27154
  · exact u27155
  · exact u27156

def b40242 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 194 324 25 19 38 102 166 294), lower := (rows 41 194 324 25 19 32 64 128 256), losses := [] }

theorem u40242 : Upper (D 6) (R 6) [40,192,320,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40243_4 : Upper (D 6) (R 6) [40,192,320,17,6,4] 13 :=
  permutation_upper _ _ _ [40,192,320,17,6,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27158

def r40243 : Route 9 := (fun mask => (mask,id))

def c40243 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40243 : Upper (D 6) (R 6) [40,192,320,17,6] 13 := by
  apply FastRouting.sound _ _ [40,192,320,17,6] 13 (by decide) (choices 1) [1,2,4] r40243 c40243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27157
  · exact u27158
  · exact m40243_4

def b40244 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 25, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 194 324 25 49 38 70 134 262), lower := (rows 41 194 324 25 49 32 64 128 256), losses := [] }

theorem u40244 : Upper (D 6) (R 6) [40,192,320,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40245 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 194 324 25 50 39 71 135 263), lower := (rows 41 194 324 25 50 32 64 128 256), losses := [] }

theorem u40245 : Upper (D 6) (R 6) [40,192,320,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40246 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 194 324 26 19 37 101 165 293), lower := (rows 41 194 324 26 19 32 64 128 256), losses := [] }

theorem u40246 : Upper (D 6) (R 6) [40,192,320,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40247 : Route 9 := (fun mask => (mask,id))

def c40247 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40247 : Upper (D 6) (R 6) [40,192,320,18,5] 13 := by
  apply FastRouting.sound _ _ [40,192,320,18,5] 13 (by decide) (choices 1) [1,2,4] r40247 c40247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27159
  · exact u27160
  · exact u27161

def b40248 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 194 324 26 22 37 101 165 293), lower := (rows 41 194 324 26 22 32 64 128 256), losses := [] }

theorem u40248 : Upper (D 6) (R 6) [40,192,320,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40249 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 194 324 26 49 39 71 135 263), lower := (rows 41 194 324 26 49 32 64 128 256), losses := [] }

theorem u40249 : Upper (D 6) (R 6) [40,192,320,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40250 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 194 324 26 50 37 69 133 261), lower := (rows 41 194 324 26 50 32 64 128 256), losses := [] }

theorem u40250 : Upper (D 6) (R 6) [40,192,320,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40251 : Route 9 := (fun mask => (mask,id))

def c40251 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40251 : Upper (D 6) (R 6) [40,192,320,18,36] 13 := by
  apply FastRouting.sound _ _ [40,192,320,18,36] 13 (by decide) (choices 1) [1,2,4] r40251 c40251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27162
  · exact u27163
  · exact u27164

def b40252 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 96 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 97 131 261 14 22 120 120 248 376), lower := (rows 97 131 261 14 22 32 64 128 256), losses := [] }

theorem u40252 : Upper (D 6) (R 6) [96,129,257,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40253 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 97 131 261 14 26 116 116 244 372), lower := (rows 97 131 261 14 26 32 64 128 256), losses := [] }

theorem u40253 : Upper (D 6) (R 6) [96,129,257,6,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40254 : Route 9 := (fun mask => (mask,id))

def c40254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40254 : Upper (D 6) (R 6) [96,129,257,6,34] 13 := by
  apply FastRouting.sound _ _ [96,129,257,6,34] 13 (by decide) (choices 1) [4,8,16,64] r40254 c40254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27165
  · exact u27166
  · exact u27167
  · exact u27168

theorem m40255_4 : Upper (D 6) (R 6) [96,129,257,6,40,4] 13 :=
  permutation_upper _ _ _ [96,129,257,6,40,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27169

def r40255 : Route 9 := (fun mask => (mask,id))

def c40255 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40255 : Upper (D 6) (R 6) [96,129,257,6,40] 13 := by
  apply FastRouting.sound _ _ [96,129,257,6,40] 13 (by decide) (choices 1) [2,4,16,64] r40255 c40255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27169
  · exact m40255_4
  · exact u27170
  · exact u27171

def b40256 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 131 261 14 112 62 94 158 286), lower := (rows 97 131 261 14 112 32 64 128 256), losses := [] }

theorem u40256 : Upper (D 6) (R 6) [96,129,257,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40257 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 131 261 26 26 100 100 228 356), lower := (rows 97 131 261 26 26 32 64 128 256), losses := [] }

theorem u40257 : Upper (D 6) (R 6) [96,129,257,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40258_4 : Upper (D 6) (R 6) [96,129,257,18,12,4] 13 :=
  permutation_upper _ _ _ [96,129,257,18,12,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27172

def r40258 : Route 9 := (fun mask => (mask,id))

def c40258 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40258 : Upper (D 6) (R 6) [96,129,257,18,12] 13 := by
  apply FastRouting.sound _ _ [96,129,257,18,12] 13 (by decide) (choices 1) [2,4,64] r40258 c40258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27172
  · exact m40258_4
  · exact u27173

def b40259 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 131 261 26 50 108 76 204 332), lower := (rows 97 131 261 26 50 32 64 128 256), losses := [] }

theorem u40259 : Upper (D 6) (R 6) [96,129,257,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u40259
end Delivery.IrregularNine14.P06
