import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0385
import IrregularNine14P07C0386
import IrregularNine14P07C0387

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37080 : Route 9 := (fun mask => (mask,id))

def c37080 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37080 : Upper (D 7) (R 7) [36,72,129,130,288] 13 := by
  apply FastRouting.sound _ _ [36,72,129,130,288] 13 (by decide) (choices 1) [1,2,16,64] r37080 c37080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23145
  · exact u23146
  · exact u23147
  · exact u23148

def r37081 : Route 9 := (fun mask => (mask,id))

def c37081 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37081 : Upper (D 7) (R 7) [36,72,129,144,3] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,3] 13 (by decide) (choices 1) [2,64,256] r37081 c37081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23149
  · exact u23150
  · exact u23151

def b37082 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 133 152 49 354 322 450 322), lower := (rows 37 74 133 152 49 32 64 128 256), losses := [] }

theorem u37082 : Upper (D 7) (R 7) [36,72,129,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37083 : Route 9 := (fun mask => (mask,id))

def c37083 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37083 : Upper (D 7) (R 7) [36,72,129,144,34] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,34] 13 (by decide) (choices 1) [1,2,64,256] r37083 c37083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23152
  · exact u23153
  · exact u23154
  · exact u23155

def b37084 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 74 133 152 81 290 354 418 290), lower := (rows 37 74 133 152 81 32 64 128 256), losses := [] }

theorem u37084 : Upper (D 7) (R 7) [36,72,129,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37085 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 133 152 82 291 355 419 291), lower := (rows 37 74 133 152 82 32 64 128 256), losses := [] }

theorem u37085 : Upper (D 7) (R 7) [36,72,129,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37086 : Route 9 := (fun mask => (mask,id))

def c37086 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37086 : Upper (D 7) (R 7) [36,72,129,144,96] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,96] 13 (by decide) (choices 1) [1,2,256] r37086 c37086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23156
  · exact u23157
  · exact u23158

def r37087 : Route 9 := (fun mask => (mask,id))

def c37087 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37087 : Upper (D 7) (R 7) [36,72,129,144,257] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,257] 13 (by decide) (choices 1) [2,64] r37087 c37087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23159
  · exact u23160

def r37088 : Route 9 := (fun mask => (mask,id))

def c37088 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37088 : Upper (D 7) (R 7) [36,72,129,144,258] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,258] 13 (by decide) (choices 1) [1,2,64] r37088 c37088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23161
  · exact u23162
  · exact u23163

def r37089 : Route 9 := (fun mask => (mask,id))

def c37089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37089 : Upper (D 7) (R 7) [36,72,129,144,288] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,288] 13 (by decide) (choices 1) [1,2,64] r37089 c37089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23164
  · exact u23165
  · exact u23166

def r37090 : Route 9 := (fun mask => (mask,id))

def c37090 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37090 : Upper (D 7) (R 7) [36,72,129,144,320] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,320] 13 (by decide) (choices 1) [1,2] r37090 c37090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23167
  · exact u23168

def r37091 : Route 9 := (fun mask => (mask,id))

def c37091 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37091 : Upper (D 7) (R 7) [36,72,129,257,34] 13 := by
  apply FastRouting.sound _ _ [36,72,129,257,34] 13 (by decide) (choices 1) [2,16,64,128] r37091 c37091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23169
  · exact u23170
  · exact u23171
  · exact u23172

def b37092 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 429, targets := 64 },{ cop := 1, region := 16, targets := 32 }], pairs := [(0,6),(2,6),(3,6),(4,5)], upper := (rows 37 74 133 265 82 178 242 178 434), lower := (rows 37 74 133 265 82 32 64 128 256), losses := [] }

theorem u37092 : Upper (D 7) (R 7) [36,72,129,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37093 : Route 9 := (fun mask => (mask,id))

def c37093 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37093 : Upper (D 7) (R 7) [36,72,129,257,96] 13 := by
  apply FastRouting.sound _ _ [36,72,129,257,96] 13 (by decide) (choices 1) [2,16,128] r37093 c37093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23173
  · exact u23174
  · exact u23175

def r37094 : Route 9 := (fun mask => (mask,id))

def c37094 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37094 : Upper (D 7) (R 7) [36,72,129,257,130] 13 := by
  apply FastRouting.sound _ _ [36,72,129,257,130] 13 (by decide) (choices 1) [2,16,64] r37094 c37094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23176
  · exact u23177
  · exact u23178

def b37095 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 265 176 114 82 210 338), lower := (rows 37 74 133 265 176 32 64 128 256), losses := [] }

theorem u37095 : Upper (D 7) (R 7) [36,72,129,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37096 : Route 9 := (fun mask => (mask,id))

def c37096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37096 : Upper (D 7) (R 7) [36,72,129,257,192] 13 := by
  apply FastRouting.sound _ _ [36,72,129,257,192] 13 (by decide) (choices 1) [2,16] r37096 c37096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23179
  · exact u23180

def b37097 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 133 266 19 240 240 240 496), lower := (rows 37 74 133 266 19 32 64 128 256), losses := [] }

theorem u37097 : Upper (D 7) (R 7) [36,72,129,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37098 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 133 266 49 242 210 210 466), lower := (rows 37 74 133 266 49 32 64 128 256), losses := [] }

theorem u37098 : Upper (D 7) (R 7) [36,72,129,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37099 : Route 9 := (fun mask => (mask,id))

def c37099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37099 : Upper (D 7) (R 7) [36,72,129,258,34] 13 := by
  apply FastRouting.sound _ _ [36,72,129,258,34] 13 (by decide) (choices 1) [1,16,64,128] r37099 c37099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23181
  · exact u23182
  · exact u23183
  · exact u23184

def r37100 : Route 9 := (fun mask => (mask,id))

def c37100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37100 : Upper (D 7) (R 7) [36,72,129,258,65] 13 := by
  apply FastRouting.sound _ _ [36,72,129,258,65] 13 (by decide) (choices 1) [2,16,128] r37100 c37100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23185
  · exact u23186
  · exact u23187

def b37101 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 133 266 82 177 241 177 433), lower := (rows 37 74 133 266 82 32 64 128 256), losses := [] }

theorem u37101 : Upper (D 7) (R 7) [36,72,129,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37102 : Route 9 := (fun mask => (mask,id))

def c37102 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37102 : Upper (D 7) (R 7) [36,72,129,258,96] 13 := by
  apply FastRouting.sound _ _ [36,72,129,258,96] 13 (by decide) (choices 1) [1,2,16,128] r37102 c37102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23188
  · exact u23189
  · exact u23190
  · exact u23191

def b37103 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 37 74 133 266 145 114 114 242 370), lower := (rows 37 74 133 266 145 32 64 128 256), losses := [] }

theorem u37103 : Upper (D 7) (R 7) [36,72,129,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37104 : Route 9 := (fun mask => (mask,id))

def c37104 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37104 : Upper (D 7) (R 7) [36,72,129,258,130] 13 := by
  apply FastRouting.sound _ _ [36,72,129,258,130] 13 (by decide) (choices 1) [1,16,64] r37104 c37104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23192
  · exact u23193
  · exact u23194

def b37105 : PairBound 9 := { available := 83, camps := [{ cop := 4, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 266 176 115 83 211 339), lower := (rows 37 74 133 266 176 32 64 128 256), losses := [] }

theorem u37105 : Upper (D 7) (R 7) [36,72,129,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37106 : Route 9 := (fun mask => (mask,id))

def c37106 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37106 : Upper (D 7) (R 7) [36,72,129,258,192] 13 := by
  apply FastRouting.sound _ _ [36,72,129,258,192] 13 (by decide) (choices 1) [1,2,16] r37106 c37106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23195
  · exact u23196
  · exact u23197

def r37107 : Route 9 := (fun mask => (mask,id))

def c37107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37107 : Upper (D 7) (R 7) [36,72,129,272,3] 13 := by
  apply FastRouting.sound _ _ [36,72,129,272,3] 13 (by decide) (choices 1) [2,64,128] r37107 c37107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23198
  · exact u23199
  · exact u23200

def b37108 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 133 280 49 226 194 194 450), lower := (rows 37 74 133 280 49 32 64 128 256), losses := [] }

theorem u37108 : Upper (D 7) (R 7) [36,72,129,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37109 : Route 9 := (fun mask => (mask,id))

def c37109 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37109 : Upper (D 7) (R 7) [36,72,129,272,34] 13 := by
  apply FastRouting.sound _ _ [36,72,129,272,34] 13 (by decide) (choices 1) [1,2,64,128] r37109 c37109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23201
  · exact u23202
  · exact u23203
  · exact u23204

def b37110 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 74 133 280 81 162 226 162 418), lower := (rows 37 74 133 280 81 32 64 128 256), losses := [] }

theorem u37110 : Upper (D 7) (R 7) [36,72,129,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37111 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 133 280 82 163 227 163 419), lower := (rows 37 74 133 280 82 32 64 128 256), losses := [] }

theorem u37111 : Upper (D 7) (R 7) [36,72,129,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37112 : Route 9 := (fun mask => (mask,id))

def c37112 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37112 : Upper (D 7) (R 7) [36,72,129,272,96] 13 := by
  apply FastRouting.sound _ _ [36,72,129,272,96] 13 (by decide) (choices 1) [1,2,128] r37112 c37112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23205
  · exact u23206
  · exact u23207

def b37113 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 37 74 133 280 145 98 98 226 354), lower := (rows 37 74 133 280 145 32 64 128 256), losses := [] }

theorem u37113 : Upper (D 7) (R 7) [36,72,129,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37114 : Route 9 := (fun mask => (mask,id))

def c37114 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37114 : Upper (D 7) (R 7) [36,72,129,272,130] 13 := by
  apply FastRouting.sound _ _ [36,72,129,272,130] 13 (by decide) (choices 1) [1,2,64] r37114 c37114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23208
  · exact u23209
  · exact u23210

def b37115 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 280 176 99 67 195 323), lower := (rows 37 74 133 280 176 32 64 128 256), losses := [] }

theorem u37115 : Upper (D 7) (R 7) [36,72,129,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37116 : Route 9 := (fun mask => (mask,id))

def c37116 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37116 : Upper (D 7) (R 7) [36,72,129,272,192] 13 := by
  apply FastRouting.sound _ _ [36,72,129,272,192] 13 (by decide) (choices 1) [1,2] r37116 c37116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23211
  · exact u23212

def r37117 : Route 9 := (fun mask => (mask,id))

def c37117 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37117 : Upper (D 7) (R 7) [36,72,129,288,3] 13 := by
  apply FastRouting.sound _ _ [36,72,129,288,3] 13 (by decide) (choices 1) [2,16,64,128] r37117 c37117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23213
  · exact u23214
  · exact u23215
  · exact u23216

def r37118 : Route 9 := (fun mask => (mask,id))

def c37118 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37118 : Upper (D 7) (R 7) [36,72,129,288,65] 13 := by
  apply FastRouting.sound _ _ [36,72,129,288,65] 13 (by decide) (choices 1) [2,16,128] r37118 c37118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23217
  · exact u23218
  · exact u23219

def b37119 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 133 296 82 179 211 147 403), lower := (rows 37 74 133 296 82 32 64 128 256), losses := [] }

theorem u37119 : Upper (D 7) (R 7) [36,72,129,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37120 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 37 74 133 296 145 114 82 210 338), lower := (rows 37 74 133 296 145 32 64 128 256), losses := [] }

theorem u37120 : Upper (D 7) (R 7) [36,72,129,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37121 : Route 9 := (fun mask => (mask,id))

def c37121 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37121 : Upper (D 7) (R 7) [36,72,129,288,130] 13 := by
  apply FastRouting.sound _ _ [36,72,129,288,130] 13 (by decide) (choices 1) [1,2,16,64] r37121 c37121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23220
  · exact u23221
  · exact u23222
  · exact u23223

def r37122 : Route 9 := (fun mask => (mask,id))

def c37122 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37122 : Upper (D 7) (R 7) [36,72,129,288,192] 13 := by
  apply FastRouting.sound _ _ [36,72,129,288,192] 13 (by decide) (choices 1) [1,2,16] r37122 c37122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23224
  · exact u23225
  · exact u23226

def r37123 : Route 9 := (fun mask => (mask,id))

def c37123 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37123 : Upper (D 7) (R 7) [36,72,129,384,3] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,3] 13 (by decide) (choices 1) [2,16,64] r37123 c37123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23227
  · exact u23228
  · exact u23229

def b37124 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 133 392 49 114 82 210 338), lower := (rows 37 74 133 392 49 32 64 128 256), losses := [] }

theorem u37124 : Upper (D 7) (R 7) [36,72,129,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37125 : Route 9 := (fun mask => (mask,id))

def c37125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37125 : Upper (D 7) (R 7) [36,72,129,384,34] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,34] 13 (by decide) (choices 1) [1,2,16,64] r37125 c37125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23230
  · exact u23231
  · exact u23232
  · exact u23233

def r37126 : Route 9 := (fun mask => (mask,id))

def c37126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37126 : Upper (D 7) (R 7) [36,72,129,384,65] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,65] 13 (by decide) (choices 1) [2,16] r37126 c37126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23234
  · exact u23235

def b37127 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 133 392 82 51 115 179 307), lower := (rows 37 74 133 392 82 32 64 128 256), losses := [] }

theorem u37127 : Upper (D 7) (R 7) [36,72,129,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37128 : Route 9 := (fun mask => (mask,id))

def c37128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37128 : Upper (D 7) (R 7) [36,72,129,384,96] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,96] 13 (by decide) (choices 1) [1,2,16] r37128 c37128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23236
  · exact u23237
  · exact u23238

def b37129 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 3, region := 370, targets := 128 },{ cop := 4, region := 484, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 37 74 134 137 19 368 368 496 368), lower := (rows 37 74 134 137 19 32 64 128 256), losses := [] }

theorem u37129 : Upper (D 7) (R 7) [36,72,130,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37130 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 134 137 49 370 338 466 338), lower := (rows 37 74 134 137 49 32 64 128 256), losses := [] }

theorem u37130 : Upper (D 7) (R 7) [36,72,130,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37131 : Route 9 := (fun mask => (mask,id))

def c37131 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37131 : Upper (D 7) (R 7) [36,72,130,129,34] 13 := by
  apply FastRouting.sound _ _ [36,72,130,129,34] 13 (by decide) (choices 1) [1,16,64,256] r37131 c37131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23239
  · exact u23240
  · exact u23241
  · exact u23242

def r37132 : Route 9 := (fun mask => (mask,id))

def c37132 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37132 : Upper (D 7) (R 7) [36,72,130,129,96] 13 := by
  apply FastRouting.sound _ _ [36,72,130,129,96] 13 (by decide) (choices 1) [1,2,16,256] r37132 c37132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23243
  · exact u23244
  · exact u23245
  · exact u23246

def r37133 : Route 9 := (fun mask => (mask,id))

def c37133 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37133 : Upper (D 7) (R 7) [36,72,130,129,257] 13 := by
  apply FastRouting.sound _ _ [36,72,130,129,257] 13 (by decide) (choices 1) [2,16,64] r37133 c37133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23247
  · exact u23248
  · exact u23249

def r37134 : Route 9 := (fun mask => (mask,id))

def c37134 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37134 : Upper (D 7) (R 7) [36,72,130,129,288] 13 := by
  apply FastRouting.sound _ _ [36,72,130,129,288] 13 (by decide) (choices 1) [1,2,16,64] r37134 c37134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23250
  · exact u23251
  · exact u23252
  · exact u23253

def b37135 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 2, region := 353, targets := 2 },{ cop := 4, region := 488, targets := 2 }], pairs := [(0,1),(0,7),(3,1),(4,7)], upper := (rows 37 74 134 152 19 353 353 481 353), lower := (rows 37 74 134 152 19 32 64 128 256), losses := [] }

theorem u37135 : Upper (D 7) (R 7) [36,72,130,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37136 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 134 152 49 355 323 451 323), lower := (rows 37 74 134 152 49 32 64 128 256), losses := [] }

theorem u37136 : Upper (D 7) (R 7) [36,72,130,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37137 : Route 9 := (fun mask => (mask,id))

def c37137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37137 : Upper (D 7) (R 7) [36,72,130,144,34] 13 := by
  apply FastRouting.sound _ _ [36,72,130,144,34] 13 (by decide) (choices 1) [1,64,256] r37137 c37137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23254
  · exact u23255
  · exact u23256

def b37138 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,7)], upper := (rows 37 74 134 152 81 291 355 419 291), lower := (rows 37 74 134 152 81 32 64 128 256), losses := [] }

theorem u37138 : Upper (D 7) (R 7) [36,72,130,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37139 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 134 152 82 289 353 417 289), lower := (rows 37 74 134 152 82 32 64 128 256), losses := [] }

theorem u37139 : Upper (D 7) (R 7) [36,72,130,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u37139
end Delivery.IrregularNine14.P07
