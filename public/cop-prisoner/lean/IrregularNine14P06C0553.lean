import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0268
import IrregularNine14P06C0269
import IrregularNine14P06C0270

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33180 : Route 9 := (fun mask => (mask,id))

def c33180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33180 : Upper (D 6) (R 6) [10,132,34,65,68] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,68] 13 (by decide) (choices 1) [1,16,256] r33180 c33180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16093
  · exact u16094
  · exact u16095

def r33181 : Route 9 := (fun mask => (mask,id))

def c33181 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33181 : Upper (D 6) (R 6) [10,132,34,65,96] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,96] 13 (by decide) (choices 1) [1,4,16,256] r33181 c33181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16096
  · exact u16097
  · exact u16098
  · exact u16099

def r33182 : Route 9 := (fun mask => (mask,id))

def c33182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33182 : Upper (D 6) (R 6) [10,132,34,65,257] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,257] 13 (by decide) (choices 1) [4,16,64] r33182 c33182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16100
  · exact u16101
  · exact u16102

def r33183 : Route 9 := (fun mask => (mask,id))

def c33183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33183 : Upper (D 6) (R 6) [10,132,34,65,260] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,260] 13 (by decide) (choices 1) [1,16,64] r33183 c33183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16103
  · exact u16104
  · exact u16105

def r33184 : Route 9 := (fun mask => (mask,id))

def c33184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33184 : Upper (D 6) (R 6) [10,132,34,65,288] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,288] 13 (by decide) (choices 1) [1,4,16,64] r33184 c33184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16106
  · exact u16107
  · exact u16108
  · exact u16109

def r33185 : Route 9 := (fun mask => (mask,id))

def c33185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33185 : Upper (D 6) (R 6) [10,132,34,65,320] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,320] 13 (by decide) (choices 1) [1,4,16] r33185 c33185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16110
  · exact u16111
  · exact u16112

def r33186 : Route 9 := (fun mask => (mask,id))

def c33186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u33186 : Upper (D 6) (R 6) [10,132,34,68,33] 13 := by
  apply FastRouting.sound _ _ [10,132,34,68,33] 13 (by decide) (choices 1) [1,16,64,256] r33186 c33186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16113
  · exact u16114
  · exact u16115
  · exact u16116

def b33187 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(4,1),(4,2)], upper := (rows 11 134 38 76 81 305 369 433 305), lower := (rows 11 134 38 76 81 32 64 128 256), losses := [] }

theorem u33187 : Upper (D 6) (R 6) [10,132,34,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33188 : Route 9 := (fun mask => (mask,id))

def c33188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33188 : Upper (D 6) (R 6) [10,132,34,68,96] 13 := by
  apply FastRouting.sound _ _ [10,132,34,68,96] 13 (by decide) (choices 1) [1,16,256] r33188 c33188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16117
  · exact u16118
  · exact u16119

def r33189 : Route 9 := (fun mask => (mask,id))

def c33189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33189 : Upper (D 6) (R 6) [10,132,34,68,257] 13 := by
  apply FastRouting.sound _ _ [10,132,34,68,257] 13 (by decide) (choices 1) [1,16,64] r33189 c33189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16120
  · exact u16121
  · exact u16122

def r33190 : Route 9 := (fun mask => (mask,id))

def c33190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33190 : Upper (D 6) (R 6) [10,132,34,68,288] 13 := by
  apply FastRouting.sound _ _ [10,132,34,68,288] 13 (by decide) (choices 1) [1,16,64] r33190 c33190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16123
  · exact u16124
  · exact u16125

def r33191 : Route 9 := (fun mask => (mask,id))

def c33191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33191 : Upper (D 6) (R 6) [10,132,34,68,320] 13 := by
  apply FastRouting.sound _ _ [10,132,34,68,320] 13 (by decide) (choices 1) [1,16] r33191 c33191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16126
  · exact u16127

def r33192 : Route 9 := (fun mask => (mask,id))

def c33192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33192 : Upper (D 6) (R 6) [10,132,34,80,5] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,5] 13 (by decide) (choices 1) [1,64,256] r33192 c33192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16128
  · exact u16129
  · exact u16130

def r33193 : Route 9 := (fun mask => (mask,id))

def c33193 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33193 : Upper (D 6) (R 6) [10,132,34,80,33] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,33] 13 (by decide) (choices 1) [1,4,64,256] r33193 c33193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16131
  · exact u16132
  · exact u16133
  · exact u16134

def b33194 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 38 88 52 353 321 449 321), lower := (rows 11 134 38 88 52 32 64 128 256), losses := [] }

theorem u33194 : Upper (D 6) (R 6) [10,132,34,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33195 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 38 88 81 293 357 421 293), lower := (rows 11 134 38 88 81 32 64 128 256), losses := [] }

theorem u33195 : Upper (D 6) (R 6) [10,132,34,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33196 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 38 88 84 289 353 417 289), lower := (rows 11 134 38 88 84 32 64 128 256), losses := [] }

theorem u33196 : Upper (D 6) (R 6) [10,132,34,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33197 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 38 88 112 293 325 389 261), lower := (rows 11 134 38 88 112 32 64 128 256), losses := [] }

theorem u33197 : Upper (D 6) (R 6) [10,132,34,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33198 : Route 9 := (fun mask => (mask,id))

def c33198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33198 : Upper (D 6) (R 6) [10,132,34,80,257] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,257] 13 (by decide) (choices 1) [1,4,64] r33198 c33198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16135
  · exact u16136
  · exact u16137

def r33199 : Route 9 := (fun mask => (mask,id))

def c33199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33199 : Upper (D 6) (R 6) [10,132,34,80,260] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,260] 13 (by decide) (choices 1) [1,64] r33199 c33199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16138
  · exact u16139

def r33200 : Route 9 := (fun mask => (mask,id))

def c33200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33200 : Upper (D 6) (R 6) [10,132,34,80,288] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80,288] 13 (by decide) (choices 1) [1,4,64] r33200 c33200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16140
  · exact u16141
  · exact u16142

def b33201 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 38 88 336 37 101 165 293), lower := (rows 11 134 38 88 336 32 64 128 256), losses := [] }

theorem u33201 : Upper (D 6) (R 6) [10,132,34,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33202 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 360, targets := 6 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,2)], upper := (rows 11 134 38 104 21 369 337 465 337), lower := (rows 11 134 38 104 21 32 64 128 256), losses := [] }

theorem u33202 : Upper (D 6) (R 6) [10,132,34,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33203 : Route 9 := (fun mask => (mask,id))

def c33203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33203 : Upper (D 6) (R 6) [10,132,34,96,65] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,65] 13 (by decide) (choices 1) [1,4,16,256] r33203 c33203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16143
  · exact u16144
  · exact u16145
  · exact u16146

def r33204 : Route 9 := (fun mask => (mask,id))

def c33204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33204 : Upper (D 6) (R 6) [10,132,34,96,68] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,68] 13 (by decide) (choices 1) [1,16,256] r33204 c33204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16147
  · exact u16148
  · exact u16149

def r33205 : Route 9 := (fun mask => (mask,id))

def c33205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33205 : Upper (D 6) (R 6) [10,132,34,96,257] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,257] 13 (by decide) (choices 1) [1,4,16,64] r33205 c33205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16150
  · exact u16151
  · exact u16152
  · exact u16153

def r33206 : Route 9 := (fun mask => (mask,id))

def c33206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33206 : Upper (D 6) (R 6) [10,132,34,96,260] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,260] 13 (by decide) (choices 1) [1,16,64] r33206 c33206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16154
  · exact u16155
  · exact u16156

def r33207 : Route 9 := (fun mask => (mask,id))

def c33207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33207 : Upper (D 6) (R 6) [10,132,34,96,320] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96,320] 13 (by decide) (choices 1) [1,4,16] r33207 c33207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16157
  · exact u16158
  · exact u16159

def b33208 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 38 265 21 112 112 240 368), lower := (rows 11 134 38 265 21 32 64 128 256), losses := [] }

theorem u33208 : Upper (D 6) (R 6) [10,132,34,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33209 : Route 9 := (fun mask => (mask,id))

def c33209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33209 : Upper (D 6) (R 6) [10,132,34,257,33] 13 := by
  apply FastRouting.sound _ _ [10,132,34,257,33] 13 (by decide) (choices 1) [4,16,64] r33209 c33209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16160
  · exact u16161
  · exact u16162

def b33210 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 38 265 52 113 81 209 337), lower := (rows 11 134 38 265 52 32 64 128 256), losses := [] }

theorem u33210 : Upper (D 6) (R 6) [10,132,34,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33211 : Route 9 := (fun mask => (mask,id))

def c33211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33211 : Upper (D 6) (R 6) [10,132,34,257,65] 13 := by
  apply FastRouting.sound _ _ [10,132,34,257,65] 13 (by decide) (choices 1) [4,16,64] r33211 c33211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16163
  · exact u16164
  · exact u16165

def r33212 : Route 9 := (fun mask => (mask,id))

def c33212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33212 : Upper (D 6) (R 6) [10,132,34,257,68] 13 := by
  apply FastRouting.sound _ _ [10,132,34,257,68] 13 (by decide) (choices 1) [1,16,64] r33212 c33212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16166
  · exact u16167
  · exact u16168

def r33213 : Route 9 := (fun mask => (mask,id))

def c33213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33213 : Upper (D 6) (R 6) [10,132,34,257,96] 13 := by
  apply FastRouting.sound _ _ [10,132,34,257,96] 13 (by decide) (choices 1) [1,4,16,64] r33213 c33213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16169
  · exact u16170
  · exact u16171
  · exact u16172

def r33214 : Route 9 := (fun mask => (mask,id))

def c33214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33214 : Upper (D 6) (R 6) [10,132,34,260,33] 13 := by
  apply FastRouting.sound _ _ [10,132,34,260,33] 13 (by decide) (choices 1) [1,16,64] r33214 c33214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16173
  · exact u16174
  · exact u16175

def r33215 : Route 9 := (fun mask => (mask,id))

def c33215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33215 : Upper (D 6) (R 6) [10,132,34,260,65] 13 := by
  apply FastRouting.sound _ _ [10,132,34,260,65] 13 (by decide) (choices 1) [1,16,64] r33215 c33215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16176
  · exact u16177
  · exact u16178

def r33216 : Route 9 := (fun mask => (mask,id))

def c33216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33216 : Upper (D 6) (R 6) [10,132,34,260,96] 13 := by
  apply FastRouting.sound _ _ [10,132,34,260,96] 13 (by decide) (choices 1) [1,16,64] r33216 c33216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16179
  · exact u16180
  · exact u16181

def r33217 : Route 9 := (fun mask => (mask,id))

def c33217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33217 : Upper (D 6) (R 6) [10,132,34,272,5] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272,5] 13 (by decide) (choices 1) [1,64] r33217 c33217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16182
  · exact u16183

def r33218 : Route 9 := (fun mask => (mask,id))

def c33218 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33218 : Upper (D 6) (R 6) [10,132,34,272,33] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272,33] 13 (by decide) (choices 1) [1,4,64] r33218 c33218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16184
  · exact u16185
  · exact u16186

def b33219 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 38 280 52 97 65 193 321), lower := (rows 11 134 38 280 52 32 64 128 256), losses := [] }

theorem u33219 : Upper (D 6) (R 6) [10,132,34,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33220 : Route 9 := (fun mask => (mask,id))

def c33220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33220 : Upper (D 6) (R 6) [10,132,34,272,65] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272,65] 13 (by decide) (choices 1) [1,4,64] r33220 c33220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16187
  · exact u16188
  · exact u16189

def r33221 : Route 9 := (fun mask => (mask,id))

def c33221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33221 : Upper (D 6) (R 6) [10,132,34,272,68] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272,68] 13 (by decide) (choices 1) [1,64] r33221 c33221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16190
  · exact u16191

def r33222 : Route 9 := (fun mask => (mask,id))

def c33222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33222 : Upper (D 6) (R 6) [10,132,34,272,96] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272,96] 13 (by decide) (choices 1) [1,4,64] r33222 c33222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16192
  · exact u16193
  · exact u16194

def b33223 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 360, targets := 6 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(3,1),(3,2)], upper := (rows 11 134 38 296 21 113 81 209 337), lower := (rows 11 134 38 296 21 32 64 128 256), losses := [] }

theorem u33223 : Upper (D 6) (R 6) [10,132,34,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33224 : Route 9 := (fun mask => (mask,id))

def c33224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33224 : Upper (D 6) (R 6) [10,132,34,288,65] 13 := by
  apply FastRouting.sound _ _ [10,132,34,288,65] 13 (by decide) (choices 1) [1,4,16,64] r33224 c33224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16195
  · exact u16196
  · exact u16197
  · exact u16198

def r33225 : Route 9 := (fun mask => (mask,id))

def c33225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33225 : Upper (D 6) (R 6) [10,132,34,288,68] 13 := by
  apply FastRouting.sound _ _ [10,132,34,288,68] 13 (by decide) (choices 1) [1,16,64] r33225 c33225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16199
  · exact u16200
  · exact u16201

def r33226 : Route 9 := (fun mask => (mask,id))

def c33226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33226 : Upper (D 6) (R 6) [10,132,34,320,5] 13 := by
  apply FastRouting.sound _ _ [10,132,34,320,5] 13 (by decide) (choices 1) [1,16,64] r33226 c33226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16202
  · exact u16203
  · exact u16204

def r33227 : Route 9 := (fun mask => (mask,id))

def c33227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33227 : Upper (D 6) (R 6) [10,132,34,320,33] 13 := by
  apply FastRouting.sound _ _ [10,132,34,320,33] 13 (by decide) (choices 1) [1,4,16,64] r33227 c33227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16205
  · exact u16206
  · exact u16207
  · exact u16208

def b33228 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 38 328 52 113 81 209 337), lower := (rows 11 134 38 328 52 32 64 128 256), losses := [] }

theorem u33228 : Upper (D 6) (R 6) [10,132,34,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33229 : Route 9 := (fun mask => (mask,id))

def c33229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33229 : Upper (D 6) (R 6) [10,132,34,320,65] 13 := by
  apply FastRouting.sound _ _ [10,132,34,320,65] 13 (by decide) (choices 1) [1,4,16] r33229 c33229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16209
  · exact u16210
  · exact u16211

def r33230 : Route 9 := (fun mask => (mask,id))

def c33230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33230 : Upper (D 6) (R 6) [10,132,34,320,68] 13 := by
  apply FastRouting.sound _ _ [10,132,34,320,68] 13 (by decide) (choices 1) [1,16] r33230 c33230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16212
  · exact u16213

def r33231 : Route 9 := (fun mask => (mask,id))

def c33231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33231 : Upper (D 6) (R 6) [10,132,34,320,96] 13 := by
  apply FastRouting.sound _ _ [10,132,34,320,96] 13 (by decide) (choices 1) [1,4,16] r33231 c33231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16214
  · exact u16215
  · exact u16216

def b33232 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 52 41 19 356 324 452 324), lower := (rows 11 134 52 41 19 32 64 128 256), losses := [] }

theorem u33232 : Upper (D 6) (R 6) [10,132,48,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33233 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 20, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 134 52 41 21 354 322 450 322), lower := (rows 11 134 52 41 21 32 64 128 256), losses := [] }

theorem u33233 : Upper (D 6) (R 6) [10,132,48,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33234 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 52 41 22 353 321 449 321), lower := (rows 11 134 52 41 22 32 64 128 256), losses := [] }

theorem u33234 : Upper (D 6) (R 6) [10,132,48,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33235 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 134 52 41 81 358 326 454 326), lower := (rows 11 134 52 41 81 32 64 128 256), losses := [] }

theorem u33235 : Upper (D 6) (R 6) [10,132,48,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33236 : Route 9 := (fun mask => (mask,id))

def c33236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33236 : Upper (D 6) (R 6) [10,132,48,33,66] 13 := by
  apply FastRouting.sound _ _ [10,132,48,33,66] 13 (by decide) (choices 1) [1,4,64,256] r33236 c33236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16217
  · exact u16218
  · exact u16219
  · exact u16220

def r33237 : Route 9 := (fun mask => (mask,id))

def c33237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33237 : Upper (D 6) (R 6) [10,132,48,33,68] 13 := by
  apply FastRouting.sound _ _ [10,132,48,33,68] 13 (by decide) (choices 1) [1,2,64,256] r33237 c33237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16221
  · exact u16222
  · exact u16223
  · exact u16224

def b33238 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 134 52 41 273 102 70 198 326), lower := (rows 11 134 52 41 273 32 64 128 256), losses := [] }

theorem u33238 : Upper (D 6) (R 6) [10,132,48,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33239 : Route 9 := (fun mask => (mask,id))

def c33239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33239 : Upper (D 6) (R 6) [10,132,48,33,258] 13 := by
  apply FastRouting.sound _ _ [10,132,48,33,258] 13 (by decide) (choices 1) [1,4,64] r33239 c33239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16225
  · exact u16226
  · exact u16227

#print axioms u33239
end Delivery.IrregularNine14.P06
