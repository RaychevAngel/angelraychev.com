import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0450
import IrregularNine14P07C0451

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39180 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 290 70 152 208 43 75 139 267), lower := (rows 37 290 70 152 208 32 64 128 256), losses := [] }

theorem u39180 : Upper (D 7) (R 7) [36,288,66,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39181 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 290 76 11 19 240 208 208 464), lower := (rows 37 290 76 11 19 32 64 128 256), losses := [] }

theorem u39181 : Upper (D 7) (R 7) [36,288,72,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39182 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,5),(3,6),(4,5)], upper := (rows 37 290 76 11 81 178 210 146 402), lower := (rows 37 290 76 11 81 32 64 128 256), losses := [] }

theorem u39182 : Upper (D 7) (R 7) [36,288,72,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39183 : Route 9 := (fun mask => (mask,id))

def c39183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39183 : Upper (D 7) (R 7) [36,288,72,3,66] 13 := by
  apply FastRouting.sound _ _ [36,288,72,3,66] 13 (by decide) (choices 1) [1,16,128] r39183 c39183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27000
  · exact u27001
  · exact u27002

def r39184 : Route 9 := (fun mask => (mask,id))

def c39184 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39184 : Upper (D 7) (R 7) [36,288,72,3,129] 13 := by
  apply FastRouting.sound _ _ [36,288,72,3,129] 13 (by decide) (choices 1) [2,16,64,128] r39184 c39184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27003
  · exact u27004
  · exact u27005
  · exact u27006

def r39185 : Route 9 := (fun mask => (mask,id))

def c39185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39185 : Upper (D 7) (R 7) [36,288,72,3,130] 13 := by
  apply FastRouting.sound _ _ [36,288,72,3,130] 13 (by decide) (choices 1) [1,16,64,128] r39185 c39185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27007
  · exact u27008
  · exact u27009
  · exact u27010

def r39186 : Route 9 := (fun mask => (mask,id))

def c39186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39186 : Upper (D 7) (R 7) [36,288,72,3,192] 13 := by
  apply FastRouting.sound _ _ [36,288,72,3,192] 13 (by decide) (choices 1) [1,2,16,128] r39186 c39186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27011
  · exact u27012
  · exact u27013
  · exact u27014

def b39187 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 194 },{ cop := 3, region := 482, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 37 290 76 25 19 226 194 194 450), lower := (rows 37 290 76 25 19 32 64 128 256), losses := [] }

theorem u39187 : Upper (D 7) (R 7) [36,288,72,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39188 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 37 290 76 25 81 162 194 130 386), lower := (rows 37 290 76 25 81 32 64 128 256), losses := [] }

theorem u39188 : Upper (D 7) (R 7) [36,288,72,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39189 : Route 9 := (fun mask => (mask,id))

def c39189 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39189 : Upper (D 7) (R 7) [36,288,72,17,66] 13 := by
  apply FastRouting.sound _ _ [36,288,72,17,66] 13 (by decide) (choices 1) [1,2,128] r39189 c39189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27015
  · exact u27016
  · exact u27017

def b39190 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 290 76 25 145 226 194 194 450), lower := (rows 37 290 76 25 145 32 64 128 256), losses := [] }

theorem u39190 : Upper (D 7) (R 7) [36,288,72,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39191 : Route 9 := (fun mask => (mask,id))

def c39191 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39191 : Upper (D 7) (R 7) [36,288,72,17,130] 13 := by
  apply FastRouting.sound _ _ [36,288,72,17,130] 13 (by decide) (choices 1) [1,2,64,128] r39191 c39191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27018
  · exact u27019
  · exact u27020
  · exact u27021

def r39192 : Route 9 := (fun mask => (mask,id))

def c39192 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39192 : Upper (D 7) (R 7) [36,288,72,17,192] 13 := by
  apply FastRouting.sound _ _ [36,288,72,17,192] 13 (by decide) (choices 1) [1,2,128] r39192 c39192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27022
  · exact u27023
  · exact u27024

def b39193 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 193 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 290 76 26 19 225 193 193 449), lower := (rows 37 290 76 26 19 32 64 128 256), losses := [] }

theorem u39193 : Upper (D 7) (R 7) [36,288,72,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39194 : Route 9 := (fun mask => (mask,id))

def c39194 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39194 : Upper (D 7) (R 7) [36,288,72,18,65] 13 := by
  apply FastRouting.sound _ _ [36,288,72,18,65] 13 (by decide) (choices 1) [1,2,128] r39194 c39194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27025
  · exact u27026
  · exact u27027

def b39195 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 37 290 76 26 82 161 193 129 385), lower := (rows 37 290 76 26 82 32 64 128 256), losses := [] }

theorem u39195 : Upper (D 7) (R 7) [36,288,72,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39196 : Route 9 := (fun mask => (mask,id))

def c39196 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39196 : Upper (D 7) (R 7) [36,288,72,18,129] 13 := by
  apply FastRouting.sound _ _ [36,288,72,18,129] 13 (by decide) (choices 1) [1,2,64,128] r39196 c39196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27028
  · exact u27029
  · exact u27030
  · exact u27031

def b39197 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 290 76 26 146 225 193 193 449), lower := (rows 37 290 76 26 146 32 64 128 256), losses := [] }

theorem u39197 : Upper (D 7) (R 7) [36,288,72,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39198 : Route 9 := (fun mask => (mask,id))

def c39198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39198 : Upper (D 7) (R 7) [36,288,72,18,192] 13 := by
  apply FastRouting.sound _ _ [36,288,72,18,192] 13 (by decide) (choices 1) [1,2,128] r39198 c39198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27032
  · exact u27033
  · exact u27034

def r39199 : Route 9 := (fun mask => (mask,id))

def c39199 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39199 : Upper (D 7) (R 7) [36,288,72,129,3] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129,3] 13 (by decide) (choices 1) [2,16,64,128] r39199 c39199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27035
  · exact u27036
  · exact u27037
  · exact u27038

def r39200 : Route 9 := (fun mask => (mask,id))

def c39200 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39200 : Upper (D 7) (R 7) [36,288,72,129,65] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129,65] 13 (by decide) (choices 1) [2,16,128] r39200 c39200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27039
  · exact u27040
  · exact u27041

def r39201 : Route 9 := (fun mask => (mask,id))

def c39201 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39201 : Upper (D 7) (R 7) [36,288,72,129,66] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129,66] 13 (by decide) (choices 1) [1,2,16,128] r39201 c39201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27042
  · exact u27043
  · exact u27044
  · exact u27045

def b39202 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 290 76 137 145 114 82 210 338), lower := (rows 37 290 76 137 145 32 64 128 256), losses := [] }

theorem u39202 : Upper (D 7) (R 7) [36,288,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39203 : Route 9 := (fun mask => (mask,id))

def c39203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39203 : Upper (D 7) (R 7) [36,288,72,129,130] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129,130] 13 (by decide) (choices 1) [1,2,16,64] r39203 c39203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27046
  · exact u27047
  · exact u27048
  · exact u27049

def r39204 : Route 9 := (fun mask => (mask,id))

def c39204 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39204 : Upper (D 7) (R 7) [36,288,72,129,192] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129,192] 13 (by decide) (choices 1) [1,2,16] r39204 c39204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27050
  · exact u27051
  · exact u27052

def r39205 : Route 9 := (fun mask => (mask,id))

def c39205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39205 : Upper (D 7) (R 7) [36,288,72,130,3] 13 := by
  apply FastRouting.sound _ _ [36,288,72,130,3] 13 (by decide) (choices 1) [1,16,64,128] r39205 c39205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27053
  · exact u27054
  · exact u27055
  · exact u27056

def r39206 : Route 9 := (fun mask => (mask,id))

def c39206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39206 : Upper (D 7) (R 7) [36,288,72,130,65] 13 := by
  apply FastRouting.sound _ _ [36,288,72,130,65] 13 (by decide) (choices 1) [1,2,16,128] r39206 c39206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27057
  · exact u27058
  · exact u27059
  · exact u27060

def r39207 : Route 9 := (fun mask => (mask,id))

def c39207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39207 : Upper (D 7) (R 7) [36,288,72,130,66] 13 := by
  apply FastRouting.sound _ _ [36,288,72,130,66] 13 (by decide) (choices 1) [1,16,128] r39207 c39207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27061
  · exact u27062
  · exact u27063

def r39208 : Route 9 := (fun mask => (mask,id))

def c39208 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39208 : Upper (D 7) (R 7) [36,288,72,130,129] 13 := by
  apply FastRouting.sound _ _ [36,288,72,130,129] 13 (by decide) (choices 1) [1,2,16,64] r39208 c39208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27064
  · exact u27065
  · exact u27066
  · exact u27067

def b39209 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 290 76 138 146 113 81 209 337), lower := (rows 37 290 76 138 146 32 64 128 256), losses := [] }

theorem u39209 : Upper (D 7) (R 7) [36,288,72,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39210 : Route 9 := (fun mask => (mask,id))

def c39210 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39210 : Upper (D 7) (R 7) [36,288,72,130,192] 13 := by
  apply FastRouting.sound _ _ [36,288,72,130,192] 13 (by decide) (choices 1) [1,2,16] r39210 c39210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27068
  · exact u27069
  · exact u27070

def r39211 : Route 9 := (fun mask => (mask,id))

def c39211 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39211 : Upper (D 7) (R 7) [36,288,72,144,3] 13 := by
  apply FastRouting.sound _ _ [36,288,72,144,3] 13 (by decide) (choices 1) [1,2,64,128] r39211 c39211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27071
  · exact u27072
  · exact u27073
  · exact u27074

def r39212 : Route 9 := (fun mask => (mask,id))

def c39212 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39212 : Upper (D 7) (R 7) [36,288,72,144,65] 13 := by
  apply FastRouting.sound _ _ [36,288,72,144,65] 13 (by decide) (choices 1) [1,2,128] r39212 c39212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27075
  · exact u27076
  · exact u27077

def r39213 : Route 9 := (fun mask => (mask,id))

def c39213 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39213 : Upper (D 7) (R 7) [36,288,72,144,66] 13 := by
  apply FastRouting.sound _ _ [36,288,72,144,66] 13 (by decide) (choices 1) [1,2,128] r39213 c39213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27078
  · exact u27079
  · exact u27080

def b39214 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 290 76 152 145 99 67 195 323), lower := (rows 37 290 76 152 145 32 64 128 256), losses := [] }

theorem u39214 : Upper (D 7) (R 7) [36,288,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39215 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 290 76 152 146 99 67 195 323), lower := (rows 37 290 76 152 146 32 64 128 256), losses := [] }

theorem u39215 : Upper (D 7) (R 7) [36,288,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39216 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(3,0)], upper := (rows 37 290 76 152 208 35 67 131 259), lower := (rows 37 290 76 152 208 32 64 128 256), losses := [] }

theorem u39216 : Upper (D 7) (R 7) [36,288,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39217 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 290 196 11 19 248 216 216 472), lower := (rows 37 290 196 11 19 32 64 128 256), losses := [] }

theorem u39217 : Upper (D 7) (R 7) [36,288,192,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39218 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 16, targets := 194 },{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5),(4,1),(4,6),(4,7)], upper := (rows 37 290 196 11 25 242 210 210 466), lower := (rows 37 290 196 11 25 32 64 128 256), losses := [] }

theorem u39218 : Upper (D 7) (R 7) [36,288,192,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39219 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 193 },{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5),(4,0),(4,6),(4,7)], upper := (rows 37 290 196 11 26 241 209 209 465), lower := (rows 37 290 196 11 26 32 64 128 256), losses := [] }

theorem u39219 : Upper (D 7) (R 7) [36,288,192,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39220 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,5),(3,6),(4,5)], upper := (rows 37 290 196 11 81 186 218 154 410), lower := (rows 37 290 196 11 81 32 64 128 256), losses := [] }

theorem u39220 : Upper (D 7) (R 7) [36,288,192,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39221 : Route 9 := (fun mask => (mask,id))

def c39221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39221 : Upper (D 7) (R 7) [36,288,192,3,66] 13 := by
  apply FastRouting.sound _ _ [36,288,192,3,66] 13 (by decide) (choices 1) [1,8,16,128] r39221 c39221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27081
  · exact u27082
  · exact u27083
  · exact u27084

def r39222 : Route 9 := (fun mask => (mask,id))

def c39222 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39222 : Upper (D 7) (R 7) [36,288,192,3,72] 13 := by
  apply FastRouting.sound _ _ [36,288,192,3,72] 13 (by decide) (choices 1) [1,2,16,128] r39222 c39222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27085
  · exact u27086
  · exact u27087
  · exact u27088

def b39223 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 290 196 11 208 59 91 155 283), lower := (rows 37 290 196 11 208 32 64 128 256), losses := [] }

theorem u39223 : Upper (D 7) (R 7) [36,288,192,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39224 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 290 196 25 25 226 194 194 450), lower := (rows 37 290 196 25 25 32 64 128 256), losses := [] }

theorem u39224 : Upper (D 7) (R 7) [36,288,192,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39225 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c39225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39225 : Upper (D 7) (R 7) [36,288,192,17,10] 13 := by
  apply FastRouting.sound _ _ [36,288,192,17,10] 13 (by decide) (choices 1) [1,2,64] r39225 c39225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27089
  · exact u27090
  · exact u27091

def b39226 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 162 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 290 196 25 81 170 202 138 394), lower := (rows 37 290 196 25 81 32 64 128 256), losses := [] }

theorem u39226 : Upper (D 7) (R 7) [36,288,192,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39227 : Route 9 := (fun mask => (mask,id))

def c39227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39227 : Upper (D 7) (R 7) [36,288,192,17,66] 13 := by
  apply FastRouting.sound _ _ [36,288,192,17,66] 13 (by decide) (choices 1) [1,2,8,128] r39227 c39227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27092
  · exact u27093
  · exact u27094
  · exact u27095

def r39228 : Route 9 := (fun mask => (mask,id))

def c39228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39228 : Upper (D 7) (R 7) [36,288,192,17,72] 13 := by
  apply FastRouting.sound _ _ [36,288,192,17,72] 13 (by decide) (choices 1) [1,2,128] r39228 c39228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27096
  · exact u27097
  · exact u27098

def b39229 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 290 196 25 208 43 75 139 267), lower := (rows 37 290 196 25 208 32 64 128 256), losses := [] }

theorem u39229 : Upper (D 7) (R 7) [36,288,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39230 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 290 196 26 26 225 193 193 449), lower := (rows 37 290 196 26 26 32 64 128 256), losses := [] }

theorem u39230 : Upper (D 7) (R 7) [36,288,192,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39231 : Route 9 := (fun mask => (mask,id))

def c39231 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39231 : Upper (D 7) (R 7) [36,288,192,18,65] 13 := by
  apply FastRouting.sound _ _ [36,288,192,18,65] 13 (by decide) (choices 1) [1,2,8,128] r39231 c39231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27099
  · exact u27100
  · exact u27101
  · exact u27102

def b39232 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 290 196 26 82 169 201 137 393), lower := (rows 37 290 196 26 82 32 64 128 256), losses := [] }

theorem u39232 : Upper (D 7) (R 7) [36,288,192,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39233 : Route 9 := (fun mask => (mask,id))

def c39233 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39233 : Upper (D 7) (R 7) [36,288,192,18,72] 13 := by
  apply FastRouting.sound _ _ [36,288,192,18,72] 13 (by decide) (choices 1) [1,2,128] r39233 c39233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27103
  · exact u27104
  · exact u27105

def b39234 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 290 196 26 208 43 75 139 267), lower := (rows 37 290 196 26 208 32 64 128 256), losses := [] }

theorem u39234 : Upper (D 7) (R 7) [36,288,192,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39235 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,6),(1,7),(3,7),(4,6)], upper := (rows 37 290 196 73 145 58 90 154 282), lower := (rows 37 290 196 73 145 32 64 128 256), losses := [] }

theorem u39235 : Upper (D 7) (R 7) [36,288,192,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39236 : Route 9 := (fun mask => (mask,id))

def c39236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39236 : Upper (D 7) (R 7) [36,288,192,65,130] 13 := by
  apply FastRouting.sound _ _ [36,288,192,65,130] 13 (by decide) (choices 1) [1,2,8,16] r39236 c39236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27106
  · exact u27107
  · exact u27108
  · exact u27109

def r39237 : Route 9 := (fun mask => (mask,id))

def c39237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39237 : Upper (D 7) (R 7) [36,288,192,65,136] 13 := by
  apply FastRouting.sound _ _ [36,288,192,65,136] 13 (by decide) (choices 1) [1,2,16] r39237 c39237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27110
  · exact u27111
  · exact u27112

theorem m39238_16 : Upper (D 7) (R 7) [36,288,192,66,130,16] 13 :=
  permutation_upper _ _ _ [36,288,192,66,130,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27114

def r39238 : Route 9 := (fun mask => (mask,id))

def c39238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39238 : Upper (D 7) (R 7) [36,288,192,66,130] 13 := by
  apply FastRouting.sound _ _ [36,288,192,66,130] 13 (by decide) (choices 1) [1,8,16] r39238 c39238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27113
  · exact u27114
  · exact m39238_16

def r39239 : Route 9 := (fun mask => (mask,id))

def c39239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39239 : Upper (D 7) (R 7) [36,288,192,66,136] 13 := by
  apply FastRouting.sound _ _ [36,288,192,66,136] 13 (by decide) (choices 1) [1,2,16] r39239 c39239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27115
  · exact u27116
  · exact u27117

#print axioms u39239
end Delivery.IrregularNine14.P07
