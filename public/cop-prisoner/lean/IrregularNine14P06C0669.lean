import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0449
import IrregularNine14P06C0450
import IrregularNine14P06C0451

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40140 : Route 9 := (fun mask => (mask,id))

def c40140 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40140 : Upper (D 6) (R 6) [40,144,288,66,5] 13 := by
  apply FastRouting.sound _ _ [40,144,288,66,5] 13 (by decide) (choices 1) [1,2,4,64] r40140 c40140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26984
  · exact u26985
  · exact u26986
  · exact u26987

def r40141 : Route 9 := (fun mask => (mask,id))

def c40141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40141 : Upper (D 6) (R 6) [40,144,288,66,6] 13 := by
  apply FastRouting.sound _ _ [40,144,288,66,6] 13 (by decide) (choices 1) [1,4,64] r40141 c40141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26988
  · exact u26989
  · exact u26990

def b40142 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 293, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 146 292 74 81 39 71 135 263), lower := (rows 41 146 292 74 81 32 64 128 256), losses := [] }

theorem u40142 : Upper (D 6) (R 6) [40,144,288,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40143 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 146 292 74 82 37 69 133 261), lower := (rows 41 146 292 74 82 32 64 128 256), losses := [] }

theorem u40143 : Upper (D 6) (R 6) [40,144,288,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40144 : Route 9 := (fun mask => (mask,id))

def c40144 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40144 : Upper (D 6) (R 6) [40,144,288,66,68] 13 := by
  apply FastRouting.sound _ _ [40,144,288,66,68] 13 (by decide) (choices 1) [1,2,4] r40144 c40144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26991
  · exact u26992
  · exact u26993

def r40145 : Route 9 := (fun mask => (mask,id))

def c40145 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40145 : Upper (D 6) (R 6) [40,144,288,68,3] 13 := by
  apply FastRouting.sound _ _ [40,144,288,68,3] 13 (by decide) (choices 1) [1,2,4,64] r40145 c40145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26994
  · exact u26995
  · exact u26996
  · exact u26997

def b40146 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 202, targets := 32 },{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(1,5),(3,5)], upper := (rows 41 146 292 76 21 99 67 195 323), lower := (rows 41 146 292 76 21 32 64 128 256), losses := [] }

theorem u40146 : Upper (D 6) (R 6) [40,144,288,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40147 : Route 9 := (fun mask => (mask,id))

def c40147 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40147 : Upper (D 6) (R 6) [40,144,288,68,6] 13 := by
  apply FastRouting.sound _ _ [40,144,288,68,6] 13 (by decide) (choices 1) [1,2,64] r40147 c40147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26998
  · exact u26999
  · exact u27000

def r40148 : Route 9 := (fun mask => (mask,id))

def c40148 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40148 : Upper (D 6) (R 6) [40,144,288,68,65] 13 := by
  apply FastRouting.sound _ _ [40,144,288,68,65] 13 (by decide) (choices 1) [1,2,4] r40148 c40148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27001
  · exact u27002
  · exact u27003

def r40149 : Route 9 := (fun mask => (mask,id))

def c40149 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40149 : Upper (D 6) (R 6) [40,144,288,68,66] 13 := by
  apply FastRouting.sound _ _ [40,144,288,68,66] 13 (by decide) (choices 1) [1,2,4] r40149 c40149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27004
  · exact u27005
  · exact u27006

def b40150 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 146 292 76 84 35 67 131 259), lower := (rows 41 146 292 76 84 32 64 128 256), losses := [] }

theorem u40150 : Upper (D 6) (R 6) [40,144,288,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40151 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 146 324 11 19 100 100 228 356), lower := (rows 41 146 324 11 19 32 64 128 256), losses := [] }

theorem u40151 : Upper (D 6) (R 6) [40,144,320,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40152 : Route 9 := (fun mask => (mask,id))

def c40152 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40152 : Upper (D 6) (R 6) [40,144,320,3,5] 13 := by
  apply FastRouting.sound _ _ [40,144,320,3,5] 13 (by decide) (choices 1) [2,4,64] r40152 c40152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27007
  · exact u27008
  · exact u27009

def r40153 : Route 9 := (fun mask => (mask,id))

def c40153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40153 : Upper (D 6) (R 6) [40,144,320,3,6] 13 := by
  apply FastRouting.sound _ _ [40,144,320,3,6] 13 (by decide) (choices 1) [1,4,64] r40153 c40153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27010
  · exact u27011
  · exact u27012

def b40154 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 146 324 11 49 102 70 198 326), lower := (rows 41 146 324 11 49 32 64 128 256), losses := [] }

theorem u40154 : Upper (D 6) (R 6) [40,144,320,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40155 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 324 11 50 101 69 197 325), lower := (rows 41 146 324 11 50 32 64 128 256), losses := [] }

theorem u40155 : Upper (D 6) (R 6) [40,144,320,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40156 : Route 9 := (fun mask => (mask,id))

def c40156 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40156 : Upper (D 6) (R 6) [40,144,320,3,36] 13 := by
  apply FastRouting.sound _ _ [40,144,320,3,36] 13 (by decide) (choices 1) [1,2,4,64] r40156 c40156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27013
  · exact u27014
  · exact u27015
  · exact u27016

def r40157 : Route 9 := (fun mask => (mask,id))

def c40157 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40157 : Upper (D 6) (R 6) [40,144,320,3,65] 13 := by
  apply FastRouting.sound _ _ [40,144,320,3,65] 13 (by decide) (choices 1) [2,4] r40157 c40157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27017
  · exact u27018

def r40158 : Route 9 := (fun mask => (mask,id))

def c40158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40158 : Upper (D 6) (R 6) [40,144,320,3,66] 13 := by
  apply FastRouting.sound _ _ [40,144,320,3,66] 13 (by decide) (choices 1) [1,4] r40158 c40158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27019
  · exact u27020

def b40159 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 146 324 11 84 39 103 167 295), lower := (rows 41 146 324 11 84 32 64 128 256), losses := [] }

theorem u40159 : Upper (D 6) (R 6) [40,144,320,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40160 : Route 9 := (fun mask => (mask,id))

def c40160 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40160 : Upper (D 6) (R 6) [40,144,320,3,96] 13 := by
  apply FastRouting.sound _ _ [40,144,320,3,96] 13 (by decide) (choices 1) [1,2,4] r40160 c40160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27021
  · exact u27022
  · exact u27023

def r40161 : Route 9 := (fun mask => (mask,id))

def c40161 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40161 : Upper (D 6) (R 6) [40,144,320,5,3] 13 := by
  apply FastRouting.sound _ _ [40,144,320,5,3] 13 (by decide) (choices 1) [2,4,64] r40161 c40161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27024
  · exact u27025
  · exact u27026

def b40162 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 146 324 13 21 98 98 226 354), lower := (rows 41 146 324 13 21 32 64 128 256), losses := [] }

theorem u40162 : Upper (D 6) (R 6) [40,144,320,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40163 : Route 9 := (fun mask => (mask,id))

def c40163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40163 : Upper (D 6) (R 6) [40,144,320,5,6] 13 := by
  apply FastRouting.sound _ _ [40,144,320,5,6] 13 (by decide) (choices 1) [1,2,64] r40163 c40163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27027
  · exact u27028
  · exact u27029

def b40164 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 146 324 13 49 102 70 198 326), lower := (rows 41 146 324 13 49 32 64 128 256), losses := [] }

theorem u40164 : Upper (D 6) (R 6) [40,144,320,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40165 : Route 9 := (fun mask => (mask,id))

def c40165 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40165 : Upper (D 6) (R 6) [40,144,320,5,34] 13 := by
  apply FastRouting.sound _ _ [40,144,320,5,34] 13 (by decide) (choices 1) [1,2,4,64] r40165 c40165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27030
  · exact u27031
  · exact u27032
  · exact u27033

def b40166 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 146 324 13 52 99 67 195 323), lower := (rows 41 146 324 13 52 32 64 128 256), losses := [] }

theorem u40166 : Upper (D 6) (R 6) [40,144,320,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40167 : Route 9 := (fun mask => (mask,id))

def c40167 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40167 : Upper (D 6) (R 6) [40,144,320,5,65] 13 := by
  apply FastRouting.sound _ _ [40,144,320,5,65] 13 (by decide) (choices 1) [2,4] r40167 c40167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27034
  · exact u27035

def r40168 : Route 9 := (fun mask => (mask,id))

def c40168 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40168 : Upper (D 6) (R 6) [40,144,320,5,66] 13 := by
  apply FastRouting.sound _ _ [40,144,320,5,66] 13 (by decide) (choices 1) [1,2,4] r40168 c40168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27036
  · exact u27037
  · exact u27038

def b40169 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 146 324 13 84 35 99 163 291), lower := (rows 41 146 324 13 84 32 64 128 256), losses := [] }

theorem u40169 : Upper (D 6) (R 6) [40,144,320,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40170 : Route 9 := (fun mask => (mask,id))

def c40170 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40170 : Upper (D 6) (R 6) [40,144,320,5,96] 13 := by
  apply FastRouting.sound _ _ [40,144,320,5,96] 13 (by decide) (choices 1) [1,2,4] r40170 c40170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27039
  · exact u27040
  · exact u27041

def r40171 : Route 9 := (fun mask => (mask,id))

def c40171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40171 : Upper (D 6) (R 6) [40,144,320,6,3] 13 := by
  apply FastRouting.sound _ _ [40,144,320,6,3] 13 (by decide) (choices 1) [1,4,64] r40171 c40171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27042
  · exact u27043
  · exact u27044

def r40172 : Route 9 := (fun mask => (mask,id))

def c40172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40172 : Upper (D 6) (R 6) [40,144,320,6,5] 13 := by
  apply FastRouting.sound _ _ [40,144,320,6,5] 13 (by decide) (choices 1) [1,2,64] r40172 c40172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27045
  · exact u27046
  · exact u27047

def b40173 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 146 324 14 22 97 97 225 353), lower := (rows 41 146 324 14 22 32 64 128 256), losses := [] }

theorem u40173 : Upper (D 6) (R 6) [40,144,320,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40174 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 146 324 14 49 103 71 199 327), lower := (rows 41 146 324 14 49 32 64 128 256), losses := [] }

theorem u40174 : Upper (D 6) (R 6) [40,144,320,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40175 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 146 324 14 50 101 69 197 325), lower := (rows 41 146 324 14 50 32 64 128 256), losses := [] }

theorem u40175 : Upper (D 6) (R 6) [40,144,320,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40176 : Route 9 := (fun mask => (mask,id))

def c40176 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40176 : Upper (D 6) (R 6) [40,144,320,6,36] 13 := by
  apply FastRouting.sound _ _ [40,144,320,6,36] 13 (by decide) (choices 1) [1,2,64] r40176 c40176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27048
  · exact u27049
  · exact u27050

def r40177 : Route 9 := (fun mask => (mask,id))

def c40177 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40177 : Upper (D 6) (R 6) [40,144,320,6,65] 13 := by
  apply FastRouting.sound _ _ [40,144,320,6,65] 13 (by decide) (choices 1) [1,2,4] r40177 c40177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27051
  · exact u27052
  · exact u27053

def b40178 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 146 324 14 82 37 101 165 293), lower := (rows 41 146 324 14 82 32 64 128 256), losses := [] }

theorem u40178 : Upper (D 6) (R 6) [40,144,320,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40179 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 146 324 14 84 35 99 163 291), lower := (rows 41 146 324 14 84 32 64 128 256), losses := [] }

theorem u40179 : Upper (D 6) (R 6) [40,144,320,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40180 : Route 9 := (fun mask => (mask,id))

def c40180 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40180 : Upper (D 6) (R 6) [40,144,320,6,96] 13 := by
  apply FastRouting.sound _ _ [40,144,320,6,96] 13 (by decide) (choices 1) [1,2,4] r40180 c40180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27054
  · exact u27055
  · exact u27056

def r40181 : Route 9 := (fun mask => (mask,id))

def c40181 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40181 : Upper (D 6) (R 6) [40,144,320,65,3] 13 := by
  apply FastRouting.sound _ _ [40,144,320,65,3] 13 (by decide) (choices 1) [2,4] r40181 c40181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27057
  · exact u27058

def b40182 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 41 146 324 73 21 38 102 166 294), lower := (rows 41 146 324 73 21 32 64 128 256), losses := [] }

theorem u40182 : Upper (D 6) (R 6) [40,144,320,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40183 : Route 9 := (fun mask => (mask,id))

def c40183 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40183 : Upper (D 6) (R 6) [40,144,320,65,6] 13 := by
  apply FastRouting.sound _ _ [40,144,320,65,6] 13 (by decide) (choices 1) [1,2,4] r40183 c40183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27059
  · exact u27060
  · exact u27061

def b40184 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 146 324 73 49 38 70 134 262), lower := (rows 41 146 324 73 49 32 64 128 256), losses := [] }

theorem u40184 : Upper (D 6) (R 6) [40,144,320,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40185 : Route 9 := (fun mask => (mask,id))

def c40185 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40185 : Upper (D 6) (R 6) [40,144,320,65,34] 13 := by
  apply FastRouting.sound _ _ [40,144,320,65,34] 13 (by decide) (choices 1) [1,2,4] r40185 c40185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27062
  · exact u27063
  · exact u27064

def r40186 : Route 9 := (fun mask => (mask,id))

def c40186 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40186 : Upper (D 6) (R 6) [40,144,320,65,36] 13 := by
  apply FastRouting.sound _ _ [40,144,320,65,36] 13 (by decide) (choices 1) [1,2,4] r40186 c40186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27065
  · exact u27066
  · exact u27067

def r40187 : Route 9 := (fun mask => (mask,id))

def c40187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40187 : Upper (D 6) (R 6) [40,144,320,66,3] 13 := by
  apply FastRouting.sound _ _ [40,144,320,66,3] 13 (by decide) (choices 1) [1,4] r40187 c40187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27068
  · exact u27069

def r40188 : Route 9 := (fun mask => (mask,id))

def c40188 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40188 : Upper (D 6) (R 6) [40,144,320,66,5] 13 := by
  apply FastRouting.sound _ _ [40,144,320,66,5] 13 (by decide) (choices 1) [1,2,4] r40188 c40188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27070
  · exact u27071
  · exact u27072

def r40189 : Route 9 := (fun mask => (mask,id))

def c40189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40189 : Upper (D 6) (R 6) [40,144,320,66,6] 13 := by
  apply FastRouting.sound _ _ [40,144,320,66,6] 13 (by decide) (choices 1) [1,4] r40189 c40189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27073
  · exact u27074

def b40190 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 146 324 74 49 39 71 135 263), lower := (rows 41 146 324 74 49 32 64 128 256), losses := [] }

theorem u40190 : Upper (D 6) (R 6) [40,144,320,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40191 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 293, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 146 324 74 50 37 69 133 261), lower := (rows 41 146 324 74 50 32 64 128 256), losses := [] }

theorem u40191 : Upper (D 6) (R 6) [40,144,320,66,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40192 : Route 9 := (fun mask => (mask,id))

def c40192 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40192 : Upper (D 6) (R 6) [40,144,320,66,36] 13 := by
  apply FastRouting.sound _ _ [40,144,320,66,36] 13 (by decide) (choices 1) [1,2,4] r40192 c40192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27075
  · exact u27076
  · exact u27077

def b40193 : PairBound 9 := { available := 86, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 324, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 162 324 13 19 118 86 214 342), lower := (rows 41 162 324 13 19 32 64 128 256), losses := [] }

theorem u40193 : Upper (D 6) (R 6) [40,160,320,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40194 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 162 324 13 21 114 82 210 338), lower := (rows 41 162 324 13 21 32 64 128 256), losses := [] }

theorem u40194 : Upper (D 6) (R 6) [40,160,320,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40195 : Route 9 := (fun mask => (mask,id))

def c40195 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40195 : Upper (D 6) (R 6) [40,160,320,5,6] 13 := by
  apply FastRouting.sound _ _ [40,160,320,5,6] 13 (by decide) (choices 1) [1,2,16,64] r40195 c40195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27078
  · exact u27079
  · exact u27080
  · exact u27081

def r40196 : Route 9 := (fun mask => (mask,id))

def c40196 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40196 : Upper (D 6) (R 6) [40,160,320,5,65] 13 := by
  apply FastRouting.sound _ _ [40,160,320,5,65] 13 (by decide) (choices 1) [2,4,16] r40196 c40196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27082
  · exact u27083
  · exact u27084

def r40197 : Route 9 := (fun mask => (mask,id))

def c40197 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40197 : Upper (D 6) (R 6) [40,160,320,5,66] 13 := by
  apply FastRouting.sound _ _ [40,160,320,5,66] 13 (by decide) (choices 1) [1,2,4,16] r40197 c40197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27085
  · exact u27086
  · exact u27087
  · exact u27088

def b40198 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 162 324 13 84 51 83 147 275), lower := (rows 41 162 324 13 84 32 64 128 256), losses := [] }

theorem u40198 : Upper (D 6) (R 6) [40,160,320,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40199 : PairBound 9 := { available := 85, camps := [{ cop := 4, region := 332, targets := 32 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(3,5)], upper := (rows 41 162 324 14 19 117 85 213 341), lower := (rows 41 162 324 14 19 32 64 128 256), losses := [] }

theorem u40199 : Upper (D 6) (R 6) [40,160,320,6,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u40199
end Delivery.IrregularNine14.P06
