import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0419
import IrregularNine14P06C0420
import IrregularNine14P06C0421

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39000 : Route 9 := (fun mask => (mask,id))

def c39000 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39000 : Upper (D 6) (R 6) [34,192,320,17,36] 13 := by
  apply FastRouting.sound _ _ [34,192,320,17,36] 13 (by decide) (choices 1) [1,2,4,8] r39000 c39000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25174
  · exact u25175
  · exact u25176
  · exact u25177

def b39001 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 324 25 56 39 71 135 263), lower := (rows 35 194 324 25 56 32 64 128 256), losses := [] }

theorem u39001 : Upper (D 6) (R 6) [34,192,320,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39002 : Route 9 := (fun mask => (mask,id))

def c39002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39002 : Upper (D 6) (R 6) [34,192,320,18,12] 13 := by
  apply FastRouting.sound _ _ [34,192,320,18,12] 13 (by decide) (choices 1) [1,4] r39002 c39002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25178
  · exact u25179

def b39003 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 324 26 49 45 77 141 269), lower := (rows 35 194 324 26 49 32 64 128 256), losses := [] }

theorem u39003 : Upper (D 6) (R 6) [34,192,320,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39004 : Route 9 := (fun mask => (mask,id))

def c39004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39004 : Upper (D 6) (R 6) [34,192,320,18,36] 13 := by
  apply FastRouting.sound _ _ [34,192,320,18,36] 13 (by decide) (choices 1) [1,4,8] r39004 c39004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25180
  · exact u25181
  · exact u25182

def b39005 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 324 26 56 37 69 133 261), lower := (rows 35 194 324 26 56 32 64 128 256), losses := [] }

theorem u39005 : Upper (D 6) (R 6) [34,192,320,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39006 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 324 28 28 35 99 163 291), lower := (rows 35 194 324 28 28 32 64 128 256), losses := [] }

theorem u39006 : Upper (D 6) (R 6) [34,192,320,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39007 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 324 28 49 47 79 143 271), lower := (rows 35 194 324 28 49 32 64 128 256), losses := [] }

theorem u39007 : Upper (D 6) (R 6) [34,192,320,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39008 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 324 28 50 45 77 141 269), lower := (rows 35 194 324 28 50 32 64 128 256), losses := [] }

theorem u39008 : Upper (D 6) (R 6) [34,192,320,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39009 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 324 28 52 43 75 139 267), lower := (rows 35 194 324 28 52 32 64 128 256), losses := [] }

theorem u39009 : Upper (D 6) (R 6) [34,192,320,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39010 : Route 9 := (fun mask => (mask,id))

def c39010 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39010 : Upper (D 6) (R 6) [34,192,320,20,40] 13 := by
  apply FastRouting.sound _ _ [34,192,320,20,40] 13 (by decide) (choices 1) [1,2,4] r39010 c39010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25183
  · exact u25184
  · exact u25185

def b39011 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 386 44 25 19 100 68 196 324), lower := (rows 35 386 44 25 19 32 64 128 256), losses := [] }

theorem u39011 : Upper (D 6) (R 6) [34,384,40,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39012 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 28, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 386 44 25 21 102 70 198 326), lower := (rows 35 386 44 25 21 32 64 128 256), losses := [] }

theorem u39012 : Upper (D 6) (R 6) [34,384,40,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39013 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 386 44 25 22 101 69 197 325), lower := (rows 35 386 44 25 22 32 64 128 256), losses := [] }

theorem u39013 : Upper (D 6) (R 6) [34,384,40,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39014 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 386 44 25 81 102 70 198 326), lower := (rows 35 386 44 25 81 32 64 128 256), losses := [] }

theorem u39014 : Upper (D 6) (R 6) [34,384,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39015 : Route 9 := (fun mask => (mask,id))

def c39015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39015 : Upper (D 6) (R 6) [34,384,40,17,66] 13 := by
  apply FastRouting.sound _ _ [34,384,40,17,66] 13 (by decide) (choices 1) [1,4,64] r39015 c39015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25186
  · exact u25187
  · exact u25188

def r39016 : Route 9 := (fun mask => (mask,id))

def c39016 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39016 : Upper (D 6) (R 6) [34,384,40,17,68] 13 := by
  apply FastRouting.sound _ _ [34,384,40,17,68] 13 (by decide) (choices 1) [1,2,4,64] r39016 c39016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25189
  · exact u25190
  · exact u25191
  · exact u25192

def b39017 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 386 44 26 21 101 69 197 325), lower := (rows 35 386 44 26 21 32 64 128 256), losses := [] }

theorem u39017 : Upper (D 6) (R 6) [34,384,40,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39018 : Route 9 := (fun mask => (mask,id))

def c39018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39018 : Upper (D 6) (R 6) [34,384,40,18,65] 13 := by
  apply FastRouting.sound _ _ [34,384,40,18,65] 13 (by decide) (choices 1) [1,4,64] r39018 c39018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25193
  · exact u25194
  · exact u25195

def r39019 : Route 9 := (fun mask => (mask,id))

def c39019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39019 : Upper (D 6) (R 6) [34,384,40,18,68] 13 := by
  apply FastRouting.sound _ _ [34,384,40,18,68] 13 (by decide) (choices 1) [1,4,64] r39019 c39019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25196
  · exact u25197
  · exact u25198

def b39020 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 386 44 28 19 101 69 197 325), lower := (rows 35 386 44 28 19 32 64 128 256), losses := [] }

theorem u39020 : Upper (D 6) (R 6) [34,384,40,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39021 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 28, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 386 44 28 21 99 67 195 323), lower := (rows 35 386 44 28 21 32 64 128 256), losses := [] }

theorem u39021 : Upper (D 6) (R 6) [34,384,40,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39022 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 386 44 28 22 97 65 193 321), lower := (rows 35 386 44 28 22 32 64 128 256), losses := [] }

theorem u39022 : Upper (D 6) (R 6) [34,384,40,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39023 : Route 9 := (fun mask => (mask,id))

def c39023 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39023 : Upper (D 6) (R 6) [34,384,40,20,65] 13 := by
  apply FastRouting.sound _ _ [34,384,40,20,65] 13 (by decide) (choices 1) [1,2,4,64] r39023 c39023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25199
  · exact u25200
  · exact u25201
  · exact u25202

def r39024 : Route 9 := (fun mask => (mask,id))

def c39024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39024 : Upper (D 6) (R 6) [34,384,40,20,66] 13 := by
  apply FastRouting.sound _ _ [34,384,40,20,66] 13 (by decide) (choices 1) [1,4,64] r39024 c39024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25203
  · exact u25204
  · exact u25205

def b39025 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 386 44 28 84 99 67 195 323), lower := (rows 35 386 44 28 84 32 64 128 256), losses := [] }

theorem u39025 : Upper (D 6) (R 6) [34,384,40,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39026 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 386 44 73 19 116 84 212 340), lower := (rows 35 386 44 73 19 32 64 128 256), losses := [] }

theorem u39026 : Upper (D 6) (R 6) [34,384,40,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39027 : PairBound 9 := { available := 86, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(3,5)], upper := (rows 35 386 44 73 21 118 86 214 342), lower := (rows 35 386 44 73 21 32 64 128 256), losses := [] }

theorem u39027 : Upper (D 6) (R 6) [34,384,40,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39028 : Route 9 := (fun mask => (mask,id))

def c39028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39028 : Upper (D 6) (R 6) [34,384,40,65,6] 13 := by
  apply FastRouting.sound _ _ [34,384,40,65,6] 13 (by decide) (choices 1) [1,4,16,64] r39028 c39028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25206
  · exact u25207
  · exact u25208
  · exact u25209

def b39029 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 386 44 73 81 54 86 150 278), lower := (rows 35 386 44 73 81 32 64 128 256), losses := [] }

theorem u39029 : Upper (D 6) (R 6) [34,384,40,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39030 : Route 9 := (fun mask => (mask,id))

def c39030 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39030 : Upper (D 6) (R 6) [34,384,40,65,66] 13 := by
  apply FastRouting.sound _ _ [34,384,40,65,66] 13 (by decide) (choices 1) [1,4,16] r39030 c39030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25210
  · exact u25211
  · exact u25212

def r39031 : Route 9 := (fun mask => (mask,id))

def c39031 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39031 : Upper (D 6) (R 6) [34,384,40,65,68] 13 := by
  apply FastRouting.sound _ _ [34,384,40,65,68] 13 (by decide) (choices 1) [1,2,4,16] r39031 c39031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25213
  · exact u25214
  · exact u25215
  · exact u25216

def r39032 : Route 9 := (fun mask => (mask,id))

def c39032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39032 : Upper (D 6) (R 6) [34,384,40,66,5] 13 := by
  apply FastRouting.sound _ _ [34,384,40,66,5] 13 (by decide) (choices 1) [1,4,16,64] r39032 c39032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25217
  · exact u25218
  · exact u25219
  · exact u25220

def r39033 : Route 9 := (fun mask => (mask,id))

def c39033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39033 : Upper (D 6) (R 6) [34,384,40,66,65] 13 := by
  apply FastRouting.sound _ _ [34,384,40,66,65] 13 (by decide) (choices 1) [1,4,16] r39033 c39033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25221
  · exact u25222
  · exact u25223

def r39034 : Route 9 := (fun mask => (mask,id))

def c39034 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39034 : Upper (D 6) (R 6) [34,384,40,66,68] 13 := by
  apply FastRouting.sound _ _ [34,384,40,66,68] 13 (by decide) (choices 1) [1,4,16] r39034 c39034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25224
  · exact u25225
  · exact u25226

def b39035 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 386 44 76 19 117 85 213 341), lower := (rows 35 386 44 76 19 32 64 128 256), losses := [] }

theorem u39035 : Upper (D 6) (R 6) [34,384,40,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39036 : PairBound 9 := { available := 83, camps := [{ cop := 4, region := 483, targets := 4 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 386 44 76 21 115 83 211 339), lower := (rows 35 386 44 76 21 32 64 128 256), losses := [] }

theorem u39036 : Upper (D 6) (R 6) [34,384,40,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39037 : Route 9 := (fun mask => (mask,id))

def c39037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39037 : Upper (D 6) (R 6) [34,384,40,68,6] 13 := by
  apply FastRouting.sound _ _ [34,384,40,68,6] 13 (by decide) (choices 1) [1,16,64] r39037 c39037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25227
  · exact u25228
  · exact u25229

def r39038 : Route 9 := (fun mask => (mask,id))

def c39038 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39038 : Upper (D 6) (R 6) [34,384,40,68,65] 13 := by
  apply FastRouting.sound _ _ [34,384,40,68,65] 13 (by decide) (choices 1) [1,2,4,16] r39038 c39038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25230
  · exact u25231
  · exact u25232
  · exact u25233

def r39039 : Route 9 := (fun mask => (mask,id))

def c39039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39039 : Upper (D 6) (R 6) [34,384,40,68,66] 13 := by
  apply FastRouting.sound _ _ [34,384,40,68,66] 13 (by decide) (choices 1) [1,4,16] r39039 c39039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25234
  · exact u25235
  · exact u25236

def b39040 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 44 76 84 51 83 147 275), lower := (rows 35 386 44 76 84 32 64 128 256), losses := [] }

theorem u39040 : Upper (D 6) (R 6) [34,384,40,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39041 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 386 44 88 19 101 69 197 325), lower := (rows 35 386 44 88 19 32 64 128 256), losses := [] }

theorem u39041 : Upper (D 6) (R 6) [34,384,40,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39042 : Route 9 := (fun mask => (mask,id))

def c39042 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39042 : Upper (D 6) (R 6) [34,384,40,80,5] 13 := by
  apply FastRouting.sound _ _ [34,384,40,80,5] 13 (by decide) (choices 1) [1,2,4,64] r39042 c39042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25237
  · exact u25238
  · exact u25239
  · exact u25240

def r39043 : Route 9 := (fun mask => (mask,id))

def c39043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39043 : Upper (D 6) (R 6) [34,384,40,80,6] 13 := by
  apply FastRouting.sound _ _ [34,384,40,80,6] 13 (by decide) (choices 1) [1,4,64] r39043 c39043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25241
  · exact u25242
  · exact u25243

def b39044 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 386 44 88 81 39 71 135 263), lower := (rows 35 386 44 88 81 32 64 128 256), losses := [] }

theorem u39044 : Upper (D 6) (R 6) [34,384,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39045 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 386 44 88 82 37 69 133 261), lower := (rows 35 386 44 88 82 32 64 128 256), losses := [] }

theorem u39045 : Upper (D 6) (R 6) [34,384,40,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39046 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 386 44 88 84 39 71 135 263), lower := (rows 35 386 44 88 84 32 64 128 256), losses := [] }

theorem u39046 : Upper (D 6) (R 6) [34,384,40,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39047 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 96 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 35 386 70 13 21 120 120 248 376), lower := (rows 35 386 70 13 21 32 64 128 256), losses := [] }

theorem u39047 : Upper (D 6) (R 6) [34,384,66,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39048 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 386 70 13 25 116 116 244 372), lower := (rows 35 386 70 13 25 32 64 128 256), losses := [] }

theorem u39048 : Upper (D 6) (R 6) [34,384,66,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39049 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 386 70 13 49 124 92 220 348), lower := (rows 35 386 70 13 49 32 64 128 256), losses := [] }

theorem u39049 : Upper (D 6) (R 6) [34,384,66,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39050 : Route 9 := (fun mask => (mask,id))

def c39050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39050 : Upper (D 6) (R 6) [34,384,66,5,36] 13 := by
  apply FastRouting.sound _ _ [34,384,66,5,36] 13 (by decide) (choices 1) [1,8,16,64] r39050 c39050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25244
  · exact u25245
  · exact u25246
  · exact u25247

def r39051 : Route 9 := (fun mask => (mask,id))

def c39051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39051 : Upper (D 6) (R 6) [34,384,66,5,40] 13 := by
  apply FastRouting.sound _ _ [34,384,66,5,40] 13 (by decide) (choices 1) [1,4,16,64] r39051 c39051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25248
  · exact u25249
  · exact u25250
  · exact u25251

def r39052 : Route 9 := (fun mask => (mask,id))

def c39052 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39052 : Upper (D 6) (R 6) [34,384,66,5,96] 13 := by
  apply FastRouting.sound _ _ [34,384,66,5,96] 13 (by decide) (choices 1) [1,4,8,16] r39052 c39052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25252
  · exact u25253
  · exact u25254
  · exact u25255

def b39053 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 386 70 25 25 100 100 228 356), lower := (rows 35 386 70 25 25 32 64 128 256), losses := [] }

theorem u39053 : Upper (D 6) (R 6) [34,384,66,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39054 : Route 9 := (fun mask => (mask,id))

def c39054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39054 : Upper (D 6) (R 6) [34,384,66,17,12] 13 := by
  apply FastRouting.sound _ _ [34,384,66,17,12] 13 (by decide) (choices 1) [1,4,64] r39054 c39054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25256
  · exact u25257
  · exact u25258

def b39055 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 386 70 25 49 108 76 204 332), lower := (rows 35 386 70 25 49 32 64 128 256), losses := [] }

theorem u39055 : Upper (D 6) (R 6) [34,384,66,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39056 : Route 9 := (fun mask => (mask,id))

def c39056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39056 : Upper (D 6) (R 6) [34,384,66,17,36] 13 := by
  apply FastRouting.sound _ _ [34,384,66,17,36] 13 (by decide) (choices 1) [1,4,8,64] r39056 c39056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25259
  · exact u25260
  · exact u25261
  · exact u25262

def b39057 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 386 70 25 56 101 69 197 325), lower := (rows 35 386 70 25 56 32 64 128 256), losses := [] }

theorem u39057 : Upper (D 6) (R 6) [34,384,66,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39058 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 386 70 25 81 44 108 172 300), lower := (rows 35 386 70 25 81 32 64 128 256), losses := [] }

theorem u39058 : Upper (D 6) (R 6) [34,384,66,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39059 : PairBound 9 := { available := 45, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 70 25 84 45 109 173 301), lower := (rows 35 386 70 25 84 32 64 128 256), losses := [] }

theorem u39059 : Upper (D 6) (R 6) [34,384,66,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u39059
end Delivery.IrregularNine14.P06
